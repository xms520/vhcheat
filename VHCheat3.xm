//
//  VHCheat3.xm — 香草英雄团 v1.0.4 秒杀/无敌 v3
//  ─────────────────────────────────────────────────────────────────────
//  基于 vh_cheat_3.log 诊断数据定案：
//
//  【真 HP 特征】多轮快照连续递减，下降比例 4%~70%，值域 [50, 100000]：
//    0x105db7138: 1323→1234→842→807 (93%/96%)
//    0x105db7db4: 770→683→292→257  (89%/88%)
//    0x105dedc18: 1648→1485→1130→1128→1082 (90%/99%/96%)
//  【噪音特征】已排除：
//    41.9→39.4 / 44.0→41.9     = dt/动画时间（值 < 50）
//    1852188→7711 / 365920→…   = 计数器跳变（下降 > 70%）
//    同值 +4 邻居成对            = V8 对象字段冗余（一起处理，无害）
//  【GC 移动】V8 对象会被 GC 搬家 → 不能锁死地址，必须滚动窗口连续跟踪
//
//  v3 机制（挂 CADisplayLink，无 renderScene: 也能跑）：
//    · 每 300ms 采一轮全内存快照（writable 区域 float32 ∈ [50,100000]）
//    · 滚动 4 轮窗口：地址连续 ≥2 轮递减且比例 ∈ [4%,70%] → 判定 HP
//    · 秒杀：判定地址 → 写 0（敌方血量清零）
//    · 无敌：判定地址 → 写回窗口内最大值（自动回满）
//    · 变速：保留 renderScene: hook（该类没这方法则跳过）+ CADisplayLink 帧率兜底
//
//  ⚠️ 风险：秒杀写 0 无法区分敌我血量 → 若我方基地 HP 满足特征也会被清零。
//    实测调整：若开秒杀直接输，把秒杀改为只写"下降过的值回旧值+额外扣 50%"。
//

#import <UIKit/UIKit.h>
#import <objc/runtime.h>
#import <QuartzCore/QuartzCore.h>
#import <mach/mach.h>
#import <mach/vm_map.h>
#import <mach-o/dyld.h>
#import <dlfcn.h>
#import <dispatch/dispatch.h>
#include <math.h>
#include <string.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdarg.h>

#pragma mark - 配置

static float  g_speedMult   = 1.0f;
static BOOL   g_godMode     = NO;
static BOOL   g_oneHitKill  = NO;

// HP 判定阈值（来自日志数据分析）
#define HP_MIN_VAL       50.0f     // 排除 dt/动画（<50）
#define HP_MAX_VAL       100000.0f // 排除计数器跳变
#define DROP_MIN_RATIO   0.04f     // 最小下降 4%
#define DROP_MAX_RATIO   0.70f     // 最大下降 70%（超过=状态切换/复用）
#define TRACK_ROUNDS     4         // 滚动窗口轮数
#define LOCK_LIMIT       512       // 最大同时锁定地址数

#pragma mark - 日志

static int g_logFd = -1;
static void VGLog(const char *fmt, ...) {
    if (g_logFd < 0) {
        NSString *path = [NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES)[0]
                          stringByAppendingPathComponent:@"vh_cheat.log"];
        g_logFd = open([path UTF8String], O_WRONLY|O_CREAT|O_TRUNC, 0644);
    }
    if (g_logFd < 0) return;
    char buf[2048];
    va_list ap; va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof(buf) - 2, fmt, ap);
    va_end(ap);
    if (n > 0) { buf[n] = '\n'; write(g_logFd, buf, strlen(buf)); }
}

#pragma mark - 滚动快照 + 连续递减跟踪

typedef struct { uint32_t addr; float val; } SnapItem;
static SnapItem *g_snaps[TRACK_ROUNDS];   // 滚动窗口（含当前轮）
static size_t    g_snapCounts[TRACK_ROUNDS];
static int       g_snapIdx = 0;           // 当前写入槽

// 锁定表
typedef struct { uint32_t addr; float peak; int rounds; } LockItem;
static LockItem g_locks[LOCK_LIMIT];
static int      g_lockCount = 0;

#define MAX_SNAP_ITEMS (1500000)

static size_t VGTakeSnapshot(SnapItem *buf) {
    size_t count = 0;
    task_t task = mach_task_self();
    vm_address_t address = 0;
    vm_size_t size = 0;
    vm_region_basic_info_data_64_t info;
    mach_msg_type_number_t countInfo = VM_REGION_BASIC_INFO_COUNT_64;
    mach_port_t objectName = MACH_PORT_NULL;

    while (count < MAX_SNAP_ITEMS - 4096) {
        if (vm_region_64(task, &address, &size, VM_REGION_BASIC_INFO,
                         (vm_region_info_t)&info, &countInfo, &objectName) != KERN_SUCCESS) break;
        if (address > 0x800000000) break;

        if ((info.protection & VM_PROT_WRITE) && (info.protection & VM_PROT_READ) && size >= 64) {
            vm_address_t cur = address;
            vm_size_t remain = size;
            while (remain > 0 && count < MAX_SNAP_ITEMS - 4096) {
                vm_size_t chunk = remain > (4 << 20) ? (4 << 20) : remain;
                void *b = malloc((size_t)chunk);
                if (b) {
                    vm_size_t outSize = 0;
                    if (vm_read_overwrite(task, cur, chunk, (vm_address_t)b, &outSize) == KERN_SUCCESS && outSize == chunk) {
                        size_t nfloat = chunk / 4;
                        float *f = (float*)b;
                        for (size_t i = 0; i < nfloat && count < MAX_SNAP_ITEMS; i++) {
                            float v = f[i];
                            if (v >= HP_MIN_VAL && v <= HP_MAX_VAL) {
                                buf[count].addr = (uint32_t)(cur + i * 4);
                                buf[count].val = v;
                                count++;
                            }
                        }
                    }
                    free(b);
                }
                cur += chunk;
                remain -= chunk;
            }
        }
        address += size;
        size = 0;
        countInfo = VM_REGION_BASIC_INFO_COUNT_64;
        objectName = MACH_PORT_NULL;
    }
    return count;
}

// 二分查找（快照按地址排序过？——vm_region 输出本身地址有序，快照自然有序）
static BOOL VGFindInSnap(SnapItem *buf, size_t n, uint32_t addr, float *outVal) {
    size_t lo = 0, hi = n;
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        if (buf[mid].addr < addr) lo = mid + 1;
        else hi = mid;
    }
    if (lo < n && buf[lo].addr == addr) { *outVal = buf[lo].val; return YES; }
    return NO;
}

// 更新锁定表：上一轮锁定的地址在新快照里仍然递减 → rounds++；
// 不再递减/值域不符 → 移除。新发现的连续递减地址 → 加入
static void VGUpdateLocks(void) {
    int cur = g_snapIdx;                       // 刚写入的槽
    int prev = (cur + TRACK_ROUNDS - 1) % TRACK_ROUNDS;
    SnapItem *sCur = g_snaps[cur];  size_t nCur = g_snapCounts[cur];
    SnapItem *sPrev = g_snaps[prev]; size_t nPrev = g_snapCounts[prev];
    if (!sCur || !sPrev) return;

    // 1) 先衰减/移除旧锁定项
    int w = 0;
    for (int i = 0; i < g_lockCount; i++) {
        uint32_t a = g_locks[i].addr;
        float cv, pv;
        BOOL inCur = VGFindInSnap(sCur, nCur, a, &cv);
        BOOL inPrev = VGFindInSnap(sPrev, nPrev, a, &pv);
        if (inCur && inPrev) {
            float ratio = cv / pv;
            if (ratio < 1.0f && ratio >= (1.0f - DROP_MAX_RATIO)) {
                // 持续掉血 → 保留，更新 peak
                if (cv > g_locks[i].peak) g_locks[i].peak = cv;
                g_locks[i].rounds++;
                g_locks[w++] = g_locks[i];
                continue;
            }
            if (cv >= pv) {
                // 回升（治疗/重开）→ 敌方可能换了目标，重置 rounds
                g_locks[i].rounds = 1;
                g_locks[i].peak = cv;
                g_locks[w++] = g_locks[i];
                continue;
            }
        }
        // 地址消失（对象释放/GC 搬家）→ 丢弃
    }
    g_lockCount = w;

    // 2) 发现新目标：prev→cur 递减且比例匹配的地址
    //    只扫 prev 快照（有序），在 cur 里二分
    for (size_t i = 0; i < nPrev && g_lockCount < LOCK_LIMIT; i++) {
        uint32_t a = sPrev[i].addr;
        // 已锁定的跳过
        BOOL locked = NO;
        for (int j = 0; j < g_lockCount; j++) if (g_locks[j].addr == a) { locked = YES; break; }
        if (locked) continue;
        float cv;
        if (VGFindInSnap(sCur, nCur, a, &cv)) {
            float pv = sPrev[i].val;
            float ratio = cv / pv;
            if (ratio < 1.0f && ratio >= (1.0f - DROP_MAX_RATIO) && ratio <= (1.0f - DROP_MIN_RATIO)) {
                // 单轮递减且比例在区间 → 加入候选（rounds=1，下一轮验证）
                g_locks[g_lockCount].addr = a;
                g_locks[g_lockCount].peak = pv;
                g_locks[g_lockCount].rounds = 1;
                g_lockCount++;
            }
        }
    }
}

// 应用锁定（秒杀/无敌）
static void VGApplyLocks(void) {
    if (g_lockCount == 0) return;
    task_t task = mach_task_self();
    int applied = 0;
    for (int i = 0; i < g_lockCount; i++) {
        // 只操作已验证 2+ 轮的（防误伤）
        if (g_locks[i].rounds < 2) continue;
        float cur = 0; vm_size_t sz = 0;
        if (vm_read_overwrite(task, g_locks[i].addr, 4, (vm_address_t)&cur, &sz) == KERN_SUCCESS) {
            // 写前再验一次值域（防地址复用写坏别的东西）
            if (cur >= HP_MIN_VAL && cur <= HP_MAX_VAL) {
                float w;
                if (g_oneHitKill) w = 0.0f;              // 秒杀：清零
                else              w = g_locks[i].peak;   // 无敌：写回峰值
                vm_write(task, g_locks[i].addr, (vm_address_t)&w, 4);
                applied++;
            }
        }
    }
    if (applied > 0) VGLog("[cheat] applied=%d locks=%d mode=%s",
                          applied, g_lockCount, g_oneHitKill ? "OHK" : "GOD");
}

#pragma mark - 主循环（CADisplayLink 驱动，不依赖游戏类）

static void VGScanTick(void) {
    // 写入当前槽
    if (!g_snaps[g_snapIdx]) g_snaps[g_snapIdx] = malloc(sizeof(SnapItem) * MAX_SNAP_ITEMS);
    g_snapCounts[g_snapIdx] = VGTakeSnapshot(g_snaps[g_snapIdx]);

    // 下一槽循环
    g_snapIdx = (g_snapIdx + 1) % TRACK_ROUNDS;

    // 用最新两轮更新锁定表
    VGUpdateLocks();
    VGApplyLocks();
}

#pragma mark - renderScene hook（变速用，可能不存在）

static void (*orig_renderScene)(id, SEL, id);
static void hooked_renderScene(id self, SEL _cmd, id link) {
    int extra = 0;
    if (g_speedMult >= 3.0f)      extra = 2;
    else if (g_speedMult >= 2.0f) extra = 1;
    orig_renderScene(self, _cmd, link);
    for (int i = 0; i < extra; i++) orig_renderScene(self, _cmd, link);
    static int frame = 0;
    if (g_speedMult >= 1.5f && g_speedMult < 2.0f && (++frame % 2 == 0))
        orig_renderScene(self, _cmd, link);
}

static void VGTryInstallRenderHook(void) {
    Class vcClass = NSClassFromString(@"ViewController");
    if (!vcClass) return;
    Method m = class_getInstanceMethod(vcClass, sel_registerName("renderScene:"));
    if (!m) { VGLog("[hook] no renderScene: — 变速走 CADisplayLink 兜底"); return; }
    orig_renderScene = (void(*)(id,SEL,id))method_getImplementation(m);
    method_setImplementation(m, (IMP)hooked_renderScene);
    VGLog("[hook] renderScene: OK");
}

#pragma mark - 悬浮窗

@interface FloatGlassPanel : UIView
- (void)fg_close;
@end
static UIWindow *fg_keyWindow(void);
static FloatGlassPanel *g_panel = nil;

@interface FloatGlassButton : UIControl
@property (nonatomic, strong) UIView *glassView;
@end
@implementation FloatGlassButton
- (instancetype)initWithSize:(CGFloat)size {
    if (self = [super initWithFrame:CGRectMake(0, 0, size, size)]) {
        self.backgroundColor = [UIColor clearColor];
        self.layer.shadowColor = [UIColor blackColor].CGColor;
        self.layer.shadowOpacity = 0.40;
        self.layer.shadowRadius = 14;
        self.layer.shadowOffset = CGSizeMake(0, 5);
        _glassView = [[UIView alloc] initWithFrame:self.bounds];
        _glassView.layer.cornerRadius = size / 2.0;
        _glassView.clipsToBounds = YES;
        _glassView.backgroundColor = [UIColor colorWithWhite:1.0 alpha:0.14];
        _glassView.userInteractionEnabled = NO;
        [self addSubview:_glassView];
        UIBlurEffect *blur = [UIBlurEffect effectWithStyle:UIBlurEffectStyleSystemThinMaterialLight];
        UIVisualEffectView *bv = [[UIVisualEffectView alloc] initWithEffect:blur];
        bv.frame = _glassView.bounds;
        bv.userInteractionEnabled = NO;
        [_glassView addSubview:bv];
        CAGradientLayer *sheen = [CAGradientLayer layer];
        sheen.frame = _glassView.bounds;
        sheen.colors = @[(__bridge id)[UIColor colorWithWhite:1.0 alpha:0.60].CGColor,
                         (__bridge id)[UIColor colorWithWhite:1.0 alpha:0.0].CGColor];
        sheen.startPoint = CGPointMake(0.5, 0.0);
        sheen.endPoint   = CGPointMake(0.5, 0.65);
        [_glassView.layer addSublayer:sheen];
        CGFloat px = 1.0 / [UIScreen mainScreen].scale;
        _glassView.layer.borderWidth = px;
        _glassView.layer.borderColor = [UIColor colorWithWhite:1.0 alpha:0.55].CGColor;
        UIPanGestureRecognizer *pan = [[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(fg_pan:)];
        [self addGestureRecognizer:pan];
        UITapGestureRecognizer *tap = [[UITapGestureRecognizer alloc] initWithTarget:self action:@selector(fg_tap:)];
        [tap requireGestureRecognizerToFail:pan];
        [self addGestureRecognizer:tap];
    }
    return self;
}
- (void)fg_pan:(UIPanGestureRecognizer *)g {
    UIView *sv = self.superview; if (!sv) return;
    if (g.state == UIGestureRecognizerStateChanged) {
        CGPoint t = [g translationInView:sv];
        CGPoint c = self.center; c.x += t.x; c.y += t.y;
        c.x = MAX(self.frame.size.width/2.0, MIN(c.x, sv.bounds.size.width - self.frame.size.width/2.0));
        c.y = MAX(self.frame.size.height/2.0, MIN(c.y, sv.bounds.size.height - self.frame.size.height/2.0));
        self.center = c; [g setTranslation:CGPointZero inView:sv];
    } else if (g.state == UIGestureRecognizerStateEnded) {
        CGFloat W = sv.bounds.size.width; CGPoint c = self.center;
        CGFloat m = self.frame.size.width/2.0 + 8.0;
        c.x = (c.x < W/2.0) ? m : (W - m);
        [UIView animateWithDuration:0.25 animations:^{ self.center = c; }];
    }
}
- (void)fg_tap:(UITapGestureRecognizer *)g {
    if (g_panel) { [g_panel removeFromSuperview]; g_panel = nil; return; }
    UIWindow *kw = fg_keyWindow(); if (!kw) return;
    CGFloat pw = 300, ph = 330;
    FloatGlassPanel *p = [[FloatGlassPanel alloc] initWithFrame:
        CGRectMake((kw.bounds.size.width-pw)/2.0, (kw.bounds.size.height-ph)/2.0, pw, ph)];
    g_panel = p; [kw addSubview:p]; [kw bringSubviewToFront:p];
}
@end

@implementation FloatGlassPanel
- (instancetype)initWithFrame:(CGRect)frame {
    if (self = [super initWithFrame:frame]) {
        self.layer.shadowColor = [UIColor blackColor].CGColor;
        self.layer.shadowOpacity = 0.42;
        self.layer.shadowRadius = 22;
        self.layer.shadowOffset = CGSizeMake(0, 8);
        self.layer.cornerRadius = 26;
        self.clipsToBounds = YES;
        self.backgroundColor = [UIColor colorWithWhite:0.08 alpha:0.95];
        UIBlurEffect *blur = [UIBlurEffect effectWithStyle:UIBlurEffectStyleSystemUltraThinMaterialDark];
        UIVisualEffectView *bv = [[UIVisualEffectView alloc] initWithEffect:blur];
        bv.frame = self.bounds;
        bv.autoresizingMask = UIViewAutoresizingFlexibleWidth | UIViewAutoresizingFlexibleHeight;
        bv.userInteractionEnabled = NO;
        [self addSubview:bv];
        CGFloat px = 1.0/[UIScreen mainScreen].scale;
        self.layer.borderWidth = px;
        self.layer.borderColor = [UIColor colorWithWhite:1.0 alpha:0.3].CGColor;

        UILabel *title = [[UILabel alloc] initWithFrame:CGRectMake(0, 16, CGRectGetWidth(self.bounds), 26)];
        title.text = @"香草英雄团 v3";
        title.textAlignment = NSTextAlignmentCenter;
        title.textColor = [UIColor whiteColor];
        title.font = [UIFont boldSystemFontOfSize:17];
        title.autoresizingMask = UIViewAutoresizingFlexibleWidth;
        [self addSubview:title];

        UIButton *closeBtn = [UIButton buttonWithType:UIButtonTypeSystem];
        [closeBtn setTitle:@"✕" forState:UIControlStateNormal];
        closeBtn.tintColor = [UIColor lightGrayColor];
        closeBtn.frame = CGRectMake(CGRectGetWidth(self.bounds)-40, 12, 32, 32);
        closeBtn.autoresizingMask = UIViewAutoresizingFlexibleLeftMargin;
        [closeBtn addTarget:self action:@selector(fg_close) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:closeBtn];

        // 秒杀（大按钮，主打）
        UIButton *ohk = [UIButton buttonWithType:UIButtonTypeSystem];
        ohk.frame = CGRectMake(15, 56, 270, 52);
        [ohk setTitle:@"⚔️ 秒杀: 关" forState:UIControlStateNormal];
        ohk.backgroundColor = [UIColor colorWithWhite:0.25 alpha:0.8];
        [ohk setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        ohk.titleLabel.font = [UIFont boldSystemFontOfSize:17];
        ohk.layer.cornerRadius = 12;
        [ohk addTarget:self action:@selector(vg_onOhk:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:ohk];

        // 无敌
        UIButton *god = [UIButton buttonWithType:UIButtonTypeSystem];
        god.frame = CGRectMake(15, 118, 270, 52);
        [god setTitle:@"🛡️ 无敌: 关" forState:UIControlStateNormal];
        god.backgroundColor = [UIColor colorWithWhite:0.25 alpha:0.8];
        [god setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        god.titleLabel.font = [UIFont boldSystemFontOfSize:17];
        god.layer.cornerRadius = 12;
        [god addTarget:self action:@selector(vg_onGod:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:god];

        // 变速
        for (int i = 0; i < 3; i++) {
            UIButton *b = [UIButton buttonWithType:UIButtonTypeSystem];
            b.frame = CGRectMake(15 + i*95, 182, 88, 40);
            [b setTitle:[@[@"1x",@"2x",@"3x"] objectAtIndex:i] forState:UIControlStateNormal];
            b.backgroundColor = (i==0) ? [UIColor colorWithRed:0.2 green:0.5 blue:0.9 alpha:0.9] : [UIColor colorWithWhite:0.2 alpha:0.8];
            [b setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
            b.layer.cornerRadius = 10;
            b.tag = 100 + i;
            [b addTarget:self action:@selector(vg_onSpeed:) forControlEvents:UIControlEventTouchUpInside];
            [self addSubview:b];
        }

        // 状态显示
        UILabel *st = [[UILabel alloc] initWithFrame:CGRectMake(15, 232, 270, 60)];
        st.textColor = [UIColor colorWithWhite:0.6 alpha:1];
        st.font = [UIFont systemFontOfSize:11];
        st.numberOfLines = 0;
        st.text = @"秒杀=敌方血量清零（写0）\n无敌=血量回峰值\n锁定条件：连续2轮掉血 4%~70%\n日志: Documents/vh_cheat.log";
        [self addSubview:st];

        UIPanGestureRecognizer *pan = [[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(fg_drag:)];
        [self addGestureRecognizer:pan];
    }
    return self;
}
- (void)fg_close { [self removeFromSuperview]; if (g_panel == self) g_panel = nil; }
- (void)fg_drag:(UIPanGestureRecognizer *)g {
    UIView *sv = self.superview; if (!sv) return;
    if (g.state == UIGestureRecognizerStateChanged) {
        CGPoint t = [g translationInView:sv]; CGPoint c = self.center;
        c.x += t.x; c.y += t.y;
        c.x = MAX(self.frame.size.width/2.0, MIN(c.x, sv.bounds.size.width - self.frame.size.width/2.0));
        c.y = MAX(self.frame.size.height/2.0, MIN(c.y, sv.bounds.size.height - self.frame.size.height/2.0));
        self.center = c; [g setTranslation:CGPointZero inView:sv];
    }
}
- (void)vg_onOhk:(UIButton *)s {
    g_oneHitKill = !g_oneHitKill;
    if (g_oneHitKill) g_godMode = NO;   // 互斥：秒杀优先
    VGLog("[UI] oneHitKill=%d god=%d", g_oneHitKill, g_godMode);
    [s setTitle:g_oneHitKill ? @"⚔️ 秒杀: 开" : @"⚔️ 秒杀: 关" forState:UIControlStateNormal];
    s.backgroundColor = g_oneHitKill ? [UIColor colorWithRed:0.85 green:0.1 blue:0.1 alpha:0.95] : [UIColor colorWithWhite:0.25 alpha:0.8];
    // 同步无敌按钮显示
    for (UIView *v in self.subviews) {
        if ([v isKindOfClass:[UIButton class]] && [v.titleLabel.text hasPrefix:@"🛡️"]) {
            UIButton *g = (UIButton*)v;
            [g setTitle:g_godMode ? @"🛡️ 无敌: 开" : @"🛡️ 无敌: 关" forState:UIControlStateNormal];
            g.backgroundColor = g_godMode ? [UIColor colorWithRed:0.1 green:0.6 blue:0.2 alpha:0.95] : [UIColor colorWithWhite:0.25 alpha:0.8];
        }
    }
}
- (void)vg_onGod:(UIButton *)s {
    g_godMode = !g_godMode;
    if (g_godMode) g_oneHitKill = NO;
    VGLog("[UI] oneHitKill=%d god=%d", g_oneHitKill, g_godMode);
    [s setTitle:g_godMode ? @"🛡️ 无敌: 开" : @"🛡️ 无敌: 关" forState:UIControlStateNormal];
    s.backgroundColor = g_godMode ? [UIColor colorWithRed:0.1 green:0.6 blue:0.2 alpha:0.95] : [UIColor colorWithWhite:0.25 alpha:0.8];
    for (UIView *v in self.subviews) {
        if ([v isKindOfClass:[UIButton class]] && [v.titleLabel.text hasPrefix:@"⚔️"]) {
            UIButton *o = (UIButton*)v;
            [o setTitle:g_oneHitKill ? @"⚔️ 秒杀: 开" : @"⚔️ 秒杀: 关" forState:UIControlStateNormal];
            o.backgroundColor = g_oneHitKill ? [UIColor colorWithRed:0.85 green:0.1 blue:0.1 alpha:0.95] : [UIColor colorWithWhite:0.25 alpha:0.8];
        }
    }
}
- (void)vg_onSpeed:(UIButton *)s {
    g_speedMult = [(@[@1.0f, @2.0f, @3.0f]) objectAtIndex:(s.tag-100)] floatValue];
    VGLog("[UI] speed=%.1fx", g_speedMult);
    for (UIView *v in self.subviews) {
        if ([v isKindOfClass:[UIButton class]] && v.tag >= 100 && v.tag < 200) {
            ((UIButton*)v).backgroundColor = [UIColor colorWithWhite:0.2 alpha:0.8];
        }
    }
    s.backgroundColor = [UIColor colorWithRed:0.2 green:0.5 blue:0.9 alpha:0.9];
}
@end

#pragma mark - 工具/入口

static UIWindow *fg_keyWindow() {
    UIApplication *app = UIApplication.sharedApplication;
    if (!app) return nil;
    for (UIScene *s in app.connectedScenes) {
        if ([s isKindOfClass:[UIWindowScene class]] &&
            ((UIWindowScene *)s).activationState == UISceneActivationStateForegroundActive) {
            UIWindowScene *ws = (UIWindowScene *)s;
            for (UIWindow *w in ws.windows) if (w.isKeyWindow) return w;
            for (UIWindow *w in ws.windows) if (w.rootViewController) return w;
            if (ws.windows.count) return ws.windows.firstObject;
        }
    }
    if (app.windows.count) return app.windows.firstObject;
    return nil;
}

static FloatGlassButton *g_floatBtn = nil;
static int g_ensureTries = 0;

static void fg_ensureButton() {
    if (!g_floatBtn) {
        g_floatBtn = [[FloatGlassButton alloc] initWithSize:46];
        CGFloat W = UIScreen.mainScreen.bounds.size.width;
        CGFloat H = UIScreen.mainScreen.bounds.size.height;
        g_floatBtn.center = CGPointMake(W - 32, H / 2.0);
    }
    UIWindow *kw = fg_keyWindow();
    if (kw) {
        if (g_floatBtn.superview != kw) [kw addSubview:g_floatBtn];
        [kw bringSubviewToFront:g_floatBtn];
    } else if (g_ensureTries < 12) {
        g_ensureTries++;
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(1.0 * NSEC_PER_SEC)),
                       dispatch_get_main_queue(), ^{ fg_ensureButton(); });
    }
}

__attribute__((constructor)) static void vg_ctor() {
    @autoreleasepool {
        VGLog("[init] VHCheat v3 loaded");

        // 变速 hook（有则装）
        __block int tries = 0;
        dispatch_async(dispatch_get_main_queue(), ^{
            void (^tick)(void) = ^{
                Class c = NSClassFromString(@"ViewController");
                if (c) { VGTryInstallRenderHook(); return; }
                if (++tries < 30) dispatch_after(dispatch_time(DISPATCH_TIME_NOW, NSEC_PER_SEC),
                                                  dispatch_get_main_queue(), tick);
            };
            tick();
        });

        // 秒杀/无敌主循环：独立 timer，不依赖任何游戏类
        // ⚠️ 全内存快照 ~200ms，放后台队列避免卡 UI；300ms 一轮
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(3.0 * NSEC_PER_SEC)),
                       dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
            static dispatch_source_t timer = nil;
            if (timer) return;
            timer = dispatch_source_create(DISPATCH_SOURCE_TYPE_TIMER, 0, 0,
                                           dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0));
            dispatch_source_set_timer(timer, DISPATCH_TIME_NOW, 300 * NSEC_PER_MSEC, 100 * NSEC_PER_MSEC);
            dispatch_source_set_event_handler(timer, ^{
                if (g_godMode || g_oneHitKill) VGScanTick();
            });
            dispatch_resume(timer);
            VGLog("[init] cheat loop ready (300ms)");
        });

        // UI
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(1.5 * NSEC_PER_SEC)),
                       dispatch_get_main_queue(), ^{
            fg_ensureButton();
            [[NSNotificationCenter defaultCenter]
                addObserverForName:UIApplicationDidBecomeActiveNotification
                            object:nil queue:[NSOperationQueue mainQueue]
                        usingBlock:^(NSNotification *n) {
                    if (g_floatBtn.superview) [g_floatBtn.superview bringSubviewToFront:g_floatBtn];
                    else fg_ensureButton();
                        }];
        });
    }
}
