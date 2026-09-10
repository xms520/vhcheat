//
//  VHCheat4.xm — 香草英雄团 v1.0.4 秒杀/无敌 v4
//  ─────────────────────────────────────────────────────────────────────
//  v3 失败根因（vh_cheat_4.log 判决：循环跑了、开关切了、0 条 applied）：
//    BUG-1 轮转方向反了：VGUpdateLocks 的 cur 取的是【下一轮要写的槽】= 旧快照，
//         prev = 新快照 → 永远在找“值上升”的地址，掉血的 HP 匹配不上
//    BUG-2 300ms 窗口太短：诊断实测 3 秒掉 ~11%，300ms 只掉 ~1% < DROP_MIN 4%
//    BUG-3 性能炸弹：新目标发现 512锁 × 150万快照双重循环 = 7.7亿次比较/轮
//
//  v4 差分引擎重构：
//    · 8 槽滚动快照 × 400ms/轮，差分窗口跨 5 轮（~2 秒，对齐诊断数据的掉血节奏）
//    · hash 桶差分 O(n)：cur 建桶，prev 查找 → 本轮“递减地址”候选集
//    · 候选连续 2 次命中（跨 ~2.4 秒持续掉血）→ 进锁定表 → 写
//    · DROP_MIN 0.3%（窗口拉长后单位掉血比例小）
//    · 状态日志每 5 轮打一行 [tick]（snap/cand/lock/applied 全链路可见）
//    · 扫描范围限制 0x100000000–0x200000000 的 RW 段（V8 堆区，日志地址全在此区间）
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

#define HP_MIN_VAL       50.0f
#define HP_MAX_VAL       100000.0f
#define DROP_MIN_RATIO   0.003f    // 0.3%（2秒窗口内小幅掉血也算）
#define DROP_MAX_RATIO   0.70f     // 超过=状态切换/地址复用
#define TRACK_ROUNDS      8        // 滚动快照槽
#define DIFF_STRIDE       5        // 差分跨 5 轮 ≈ 2 秒
#define CAND_LIMIT        4096      // 候选表上限
#define LOCK_LIMIT        512       // 锁定表上限
#define SCAN_ADDR_MIN     0x100000000ULL
#define SCAN_ADDR_MAX     0x200000000ULL
#define TICK_MS           400       // 扫描周期

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

#pragma mark - 快照

typedef struct { uint32_t addr; float val; } SnapItem;
static SnapItem *g_snaps[TRACK_ROUNDS];
static size_t    g_snapCounts[TRACK_ROUNDS];
static int       g_writeSlot  = 0;
static int       g_filledRounds = 0;   // 已采集轮数（>= DIFF_STRIDE+1 才能差分）

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
        // 范围限制：V8 堆区（诊断日志地址 0x101~0x108 全在此）
        if (address >= SCAN_ADDR_MAX) break;
        if (address + size > SCAN_ADDR_MIN &&
            (info.protection & VM_PROT_WRITE) && (info.protection & VM_PROT_READ) && size >= 64) {
            vm_address_t cur = (address < SCAN_ADDR_MIN) ? SCAN_ADDR_MIN : address;
            vm_address_t end = address + size;
            if (end > SCAN_ADDR_MAX) end = SCAN_ADDR_MAX;
            vm_size_t remain = end - cur;
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

#pragma mark - 候选表 + 锁定表

// 候选：本轮差分发现“在掉”的地址，连续 hits 次进锁定
typedef struct { uint32_t addr; float peak; float lastVal; int hits; } CandItem;
static CandItem g_cands[CAND_LIMIT];
static int      g_candCount = 0;

// 锁定：确认的 HP 地址
typedef struct { uint32_t addr; float peak; } LockItem;
static LockItem g_locks[LOCK_LIMIT];
static int       g_lockCount = 0;

// 差分 hash 桶（对 cur 快照建索引）
#define HB_BITS 21
#define HB_SIZE (1u << HB_BITS)
#define HB_MASK (HB_SIZE - 1)
static uint32_t *hHead = NULL;   // 桶头 → cur 下标+1（0=空）
static uint32_t *hNext = NULL;   // 链 next

static BOOL VGHashInit(void) {
    if (!hHead) hHead = calloc(HB_SIZE, sizeof(uint32_t));
    if (!hNext) hNext = calloc(MAX_SNAP_ITEMS, sizeof(uint32_t));
    return hHead && hNext;
}

// 一轮差分：cur(新) vs prev(旧，DIFF_STRIDE 轮前) → 维护候选/锁定 → 应用写
static int g_appliedLast = 0;
static int g_tickCount = 0;

static void VGDifferential(int curSlot, int prevSlot) {
    SnapItem *sCur  = g_snaps[curSlot];   size_t nCur  = g_snapCounts[curSlot];
    SnapItem *sPrev = g_snaps[prevSlot]; size_t nPrev = g_snapCounts[prevSlot];
    if (!sCur || !sPrev || nCur < 2 || nPrev < 2) return;
    if (!VGHashInit()) return;

    // 1. cur 建桶
    memset(hHead, 0, HB_SIZE * sizeof(uint32_t));
    for (uint32_t i = 0; i < nCur; i++) {
        uint32_t h = (g_snaps[curSlot][i].addr >> 2) & HB_MASK;
        hNext[i] = hHead[h];
        hHead[h] = i + 1;
    }

    // 2. 遍历 prev，在 cur 查找 → 下降 [0.3%, 70%] 的地址进本轮命中集
    //    命中集直接在候选表上更新（旧候选 hits++，新地址 hits=1，未命中移除）
    int w = 0;   // 候选表压缩写指针
    int newCand = 0, promoted = 0;
    int hitFlags[CAND_LIMIT];     // 候选本轮是否命中（下标对齐候选表）
    memset(hitFlags, 0, sizeof(hitFlags));

    for (size_t i = 0; i < nPrev; i++) {
        uint32_t a = sPrev[i].addr;
        float pv = sPrev[i].val;
        uint32_t h = (a >> 2) & HB_MASK;
        for (uint32_t j = hHead[h]; j != 0; j = hNext[j - 1]) {
            SnapItem *ci = &sCur[j - 1];
            if (ci->addr == a) {
                float cv = ci->val;
                if (cv < pv) {
                    float ratio = 1.0f - cv / pv;
                    if (ratio >= DROP_MIN_RATIO && ratio <= DROP_MAX_RATIO) {
                        // 本轮在掉 → 查候选表
                        int found = -1;
                        for (int k = 0; k < g_candCount; k++) {
                            if (g_cands[k].addr == a) { found = k; break; }
                        }
                        if (found >= 0) {
                            hitFlags[found] = 1;
                            g_cands[found].lastVal = cv;
                            if (pv > g_cands[found].peak) g_cands[found].peak = pv;
                            g_cands[found].hits++;
                        } else if (g_candCount < CAND_LIMIT) {
                            g_cands[g_candCount].addr = a;
                            g_cands[g_candCount].peak = pv;
                            g_cands[g_candCount].lastVal = cv;
                            g_cands[g_candCount].hits = 1;
                            hitFlags[g_candCount] = 1;
                            g_candCount++;
                            newCand++;
                        }
                    }
                }
                break;   // 地址唯一（同快照内地址重复概率极低，取第一个）
            }
        }
    }

    // 3. 候选表压缩：未命中的丢弃；hits>=2 的晋升锁定
    for (int k = 0; k < g_candCount; k++) {
        if (!hitFlags[k]) continue;                       // 本轮没掉 → 丢弃
        if (g_cands[k].hits >= 2) {                        // 连续 2 轮掉 → 锁定
            BOOL exists = NO;
            for (int m = 0; m < g_lockCount; m++) {
                if (g_locks[m].addr == g_cands[k].addr) {
                    exists = YES;
                    if (g_cands[k].peak > g_locks[m].peak) g_locks[m].peak = g_cands[k].peak;
                    break;
                }
            }
            if (!exists && g_lockCount < LOCK_LIMIT) {
                g_locks[g_lockCount].addr = g_cands[k].addr;
                g_locks[g_lockCount].peak = g_cands[k].peak;
                g_lockCount++;
                promoted++;
            }
        }
        g_cands[w++] = g_cands[k];   // 保留还在掉的候选（未达 2 次的下次继续累积）
    }
    g_candCount = w;

    // 4. 锁定表维护：地址消失/值域漂移 → 移除（写时也会二次验证）
    //    （GC 搬家后地址会消失，靠候选重新发现，无需特殊处理）

    // 5. 应用写（秒杀=0 / 无敌=peak），写前验证值域防地址复用
    g_appliedLast = 0;
    if (g_godMode || g_oneHitKill) {
        task_t task = mach_task_self();
        for (int m = 0; m < g_lockCount; m++) {
            float curV = 0; vm_size_t sz = 0;
            if (vm_read_overwrite(task, g_locks[m].addr, 4, (vm_address_t)&curV, &sz) == KERN_SUCCESS) {
                if (curV >= HP_MIN_VAL && curV <= HP_MAX_VAL) {
                    float wv = g_oneHitKill ? 0.0f : g_locks[m].peak;
                    vm_write(task, g_locks[m].addr, (vm_address_t)&wv, 4);
                    g_appliedLast++;
                }
            }
        }
    }

    // 6. 状态日志（每 5 轮 = ~2 秒一条）
    g_tickCount++;
    if (g_tickCount % 5 == 0) {
        VGLog("[tick] snap=%zu cand=%d(new %d) lock=%d(prom %d) applied=%d mode=%s",
              nCur, g_candCount, newCand, g_lockCount, promoted, g_appliedLast,
              g_oneHitKill ? "OHK" : (g_godMode ? "GOD" : "off"));
    }
}

static void VGScanTick(void) {
    // 重入保护：上一轮扫描没跑完（内存大/机器慢）就跳过本次触发，
    // 防止 GCD 队列任务堆积拖死主线程（v3 面板失灵的根因）
    static volatile int scanning = 0;
    if (__sync_lock_test_and_set(&scanning, 1)) return;

    int slot = g_writeSlot;
    if (!g_snaps[slot]) g_snaps[slot] = malloc(sizeof(SnapItem) * MAX_SNAP_ITEMS);
    g_snapCounts[slot] = VGTakeSnapshot(g_snaps[slot]);
    g_writeSlot = (slot + 1) % TRACK_ROUNDS;

    if (g_filledRounds > DIFF_STRIDE) {
        // cur = 刚写的槽（v3 的方向 bug 修正）
        int curSlot  = slot;
        int prevSlot = (slot + TRACK_ROUNDS - DIFF_STRIDE) % TRACK_ROUNDS;
        VGDifferential(curSlot, prevSlot);
    }
    g_filledRounds++;
    scanning = 0;
}

#pragma mark - 变速（renderScene 有则 hook，无则放弃）

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
    if (!m) { VGLog("[hook] no renderScene: (变速不可用，秒杀/无敌不受影响)"); return; }
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
    // 点按切换面板（面板未挂载/已移除 → 打开；存在 → 关闭）
    if (g_panel && g_panel.superview) {
        [g_panel removeFromSuperview];
        g_panel = nil;
        return;
    }
    g_panel = nil;   // 清掉僵尸引用
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
        title.text = @"香草英雄团 v4";
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

        UIButton *ohk = [UIButton buttonWithType:UIButtonTypeSystem];
        ohk.frame = CGRectMake(15, 56, 270, 52);
        [ohk setTitle:@"⚔️ 秒杀: 关" forState:UIControlStateNormal];
        ohk.backgroundColor = [UIColor colorWithWhite:0.25 alpha:0.8];
        [ohk setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        ohk.titleLabel.font = [UIFont boldSystemFontOfSize:17];
        ohk.layer.cornerRadius = 12;
        [ohk addTarget:self action:@selector(vg_onOhk:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:ohk];

        UIButton *god = [UIButton buttonWithType:UIButtonTypeSystem];
        god.frame = CGRectMake(15, 118, 270, 52);
        [god setTitle:@"🛡️ 无敌: 关" forState:UIControlStateNormal];
        god.backgroundColor = [UIColor colorWithWhite:0.25 alpha:0.8];
        [god setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        god.titleLabel.font = [UIFont boldSystemFontOfSize:17];
        god.layer.cornerRadius = 12;
        [god addTarget:self action:@selector(vg_onGod:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:god];

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

        UILabel *st = [[UILabel alloc] initWithFrame:CGRectMake(15, 232, 270, 80)];
        st.textColor = [UIColor colorWithWhite:0.6 alpha:1];
        st.font = [UIFont systemFontOfSize:11];
        st.numberOfLines = 0;
        st.text = @"锁定：2秒窗口持续掉血 0.3%~70%\n秒杀=清零 | 无敌=回峰值\n每2秒打一条 [tick] 状态到日志";
        [self addSubview:st];

        UIPanGestureRecognizer *pan = [[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(fg_drag:)];
        [self addGestureRecognizer:pan];
    }
    return self;
}
- (void)fg_close {
    [self removeFromSuperview];
    if (g_panel == self) g_panel = nil;   // 同步清全局引用，防僵尸面板卡状态
}
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
    if (g_oneHitKill) g_godMode = NO;
    VGLog("[UI] oneHitKill=%d god=%d", g_oneHitKill, g_godMode);
    [s setTitle:g_oneHitKill ? @"⚔️ 秒杀: 开" : @"⚔️ 秒杀: 关" forState:UIControlStateNormal];
    s.backgroundColor = g_oneHitKill ? [UIColor colorWithRed:0.85 green:0.1 blue:0.1 alpha:0.95] : [UIColor colorWithWhite:0.25 alpha:0.8];
    for (UIView *v in self.subviews) {
        if ([v isKindOfClass:[UIButton class]] && [((UIButton *)v).titleLabel.text hasPrefix:@"🛡️"]) {
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
        if ([v isKindOfClass:[UIButton class]] && [((UIButton *)v).titleLabel.text hasPrefix:@"⚔️"]) {
            UIButton *o = (UIButton*)v;
            [o setTitle:g_oneHitKill ? @"⚔️ 秒杀: 开" : @"⚔️ 秒杀: 关" forState:UIControlStateNormal];
            o.backgroundColor = g_oneHitKill ? [UIColor colorWithRed:0.85 green:0.1 blue:0.1 alpha:0.95] : [UIColor colorWithWhite:0.25 alpha:0.8];
        }
    }
}
- (void)vg_onSpeed:(UIButton *)s {
    NSArray *vals = @[@1.0f, @2.0f, @3.0f];
    g_speedMult = [vals[s.tag - 100] floatValue];
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
        VGLog("[init] VHCheat v4 loaded");

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

        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(3.0 * NSEC_PER_SEC)),
                       dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
            static dispatch_source_t timer = nil;
            if (timer) return;
            timer = dispatch_source_create(DISPATCH_SOURCE_TYPE_TIMER, 0, 0,
                                           dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0));
            dispatch_source_set_timer(timer, DISPATCH_TIME_NOW,
                                      (uint64_t)TICK_MS * NSEC_PER_MSEC,
                                      (uint64_t)100 * NSEC_PER_MSEC);
            dispatch_source_set_event_handler(timer, ^{ VGScanTick(); });
            dispatch_resume(timer);
            VGLog("[init] cheat loop ready (%dms, diff window ~%.1fs)",
                  TICK_MS, TICK_MS * DIFF_STRIDE / 1000.0);
        });

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
