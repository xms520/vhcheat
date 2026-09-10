//
//  VHCheat5.xm — 香草英雄团 v1.0.4 秒杀/无敌 v5
//  ─────────────────────────────────────────────────────────────────────
//  v4 失败根因（vh_cheat_4.log [tick] 行判决）：
//    R1 锁定表只进不出：prom 454 填满 512 后永不再刷新，
//       秒杀开启时表内全是开启前的僵尸地址 → 读值越界 → applied=0
//    R2 snap=1500000 恒等于容量上限 = 扫描被截断且截断点漂移
//       → 后段地址扫不到 + 产生 new 4047 假候选抖动
//    R3 “秒杀自动关闭” = 面板按钮文字写死“关”，重开面板显示不同步
//       （g_oneHitKill 从未被重置，纯显示 bug）
//
//  v5 重构：
//    · 废除锁定表 —— 直接对本窗口「连续 2 次掉血」候选实时写（地址永远是新鲜的）
//    · MAX_SNAP_ITEMS 1.5M → 2.5M（v2 诊断 2M 才扫到 0x108f 区，1.5M 必截断）
//    · 槽 8 → 6（DIFF_STRIDE 5 不变，省 40MB 内存）
//    · 候选容忍 1 次未命中（爆发型掉血不丢目标）
//    · 面板打开时同步真实开关状态（按钮文字/颜色来自全局 flag）
//    · [hit] 日志：每次实际写入打一条（addr old→new mode），效果直接可见
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

#define HP_MIN_VAL       100.0f
#define HP_MAX_VAL       20000.0f
#define DROP_MIN_RATIO   0.003f
#define DROP_MAX_RATIO   0.70f
#define ZONES            8         // 扫描区分 8 区轮扫
#define ZONE_SIZE        0x20000000ULL  // 512MB/区（8×512M=4GB 全覆盖）
#define SNAP_PER_ZONE     2         // 每区 2 槽（cur/prev，间隔 ZONES 轮=3.2s）
#define CAND_LIMIT        8192
#define MAX_SNAP_ITEMS    600000   // 60万/区：512MB 内 [100,20000] 浮点 << 60万 → 不截断
#define APPLY_PER_TICK    4096
#define SCAN_ADDR_MIN     0x100000000ULL
#define SCAN_ADDR_MAX     0x200000000ULL
#define TICK_MS           400

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

typedef struct { uint64_t addr; float val; } SnapItem;
static SnapItem *g_snaps[ZONES][SNAP_PER_ZONE];   // 每区 2 槽
static size_t    g_snapCounts[ZONES][SNAP_PER_ZONE];
static int       g_curZone    = 0;
static int       g_zoneFill[ZONES];

static size_t VGScanZone(int zone, SnapItem *buf) {
    uint64_t zBase = SCAN_ADDR_MIN + (uint64_t)zone * ZONE_SIZE;
    uint64_t zEnd  = zBase + ZONE_SIZE;
    if (zEnd > SCAN_ADDR_MAX) zEnd = SCAN_ADDR_MAX;
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
        if (address >= zEnd) break;
        if (address + size > zBase &&
            (info.protection & VM_PROT_WRITE) && (info.protection & VM_PROT_READ) && size >= 64) {
            vm_address_t cur = (address < zBase) ? zBase : address;
            vm_address_t end = address + size;
            if (end > zEnd) end = zEnd;
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
                                buf[count].addr = (uint64_t)(cur + i * 4);
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

#pragma mark - 候选表（v5：无锁定表，候选即真相）

// hits：累计命中“下降窗口”次数；misses：连续未命中次数（容忍 1 次）
typedef struct { uint64_t addr; float peak; float lastVal; int hits; int misses; char hitThis; int zone; } CandItem;
static CandItem g_cands[CAND_LIMIT];
static int      g_candCount = 0;

#define HB_BITS 21
#define HB_SIZE (1u << HB_BITS)
#define HB_MASK (HB_SIZE - 1)
static uint32_t *hHead = NULL;
static uint32_t *hNext = NULL;

static BOOL VGHashInit(void) {
    if (!hHead) hHead = calloc(HB_SIZE, sizeof(uint32_t));
    if (!hNext) hNext = calloc(MAX_SNAP_ITEMS, sizeof(uint32_t));
    return hHead && hNext;
}

static int g_appliedLast = 0;
static int g_tickCount = 0;

// v9: 写后回读检测帧覆盖
#define RECHECK_MAX 4096
static uint64_t g_writtenLast[RECHECK_MAX];   // 上一轮写入的地址
static int       g_writtenCount = 0;

static void VGDifferentialZone(int zone) {
    // v9: 回读上一轮写入的地址 —— 值非 0 = 被游戏重算覆盖
    if (g_writtenCount > 0) {
        task_t t = mach_task_self();
        int reverted = 0, still0 = 0, gone = 0;
        for (int i = 0; i < g_writtenCount && i < RECHECK_MAX; i++) {
            float v = 0; vm_size_t sz = 0;
            if (vm_read_overwrite(t, g_writtenLast[i], 4, (vm_address_t)&v, &sz) == KERN_SUCCESS) {
                if (v < 0.0001f) still0++;
                else if (v >= HP_MIN_VAL && v <= HP_MAX_VAL) reverted++;
                else gone++;
            } else gone++;
        }
        if (reverted > 0)
            VGLog("[recheck] reverted=%d still0=%d gone=%d ← reverted>0=帧重算覆盖实锤",
                  reverted, still0, gone);
        g_writtenCount = 0;
    }

    SnapItem *sCur  = g_snaps[zone][0];   size_t nCur  = g_snapCounts[zone][0];
    SnapItem *sPrev = g_snaps[zone][1]; size_t nPrev = g_snapCounts[zone][1];
    if (!sCur || !sPrev || nCur < 2 || nPrev < 2) return;
    if (!VGHashInit()) return;

    // 1. cur 建 hash 桶
    memset(hHead, 0, HB_SIZE * sizeof(uint32_t));
    for (uint32_t i = 0; i < nCur; i++) {
        uint32_t h = (uint32_t)((sCur[i].addr >> 2) & HB_MASK);
        hNext[i] = hHead[h];
        hHead[h] = i + 1;
    }

    // 2. 重置本区候选命中标记
    for (int k = 0; k < g_candCount; k++)
        if (g_cands[k].zone == zone) g_cands[k].hitThis = 0;

    // 3. 区内 diff：prev→cur 下降 [0.3%,70%] → 更新/新增候选
    int newCand = 0;
    for (size_t i = 0; i < nPrev; i++) {
        uint64_t a = sPrev[i].addr;
        float pv = sPrev[i].val;
        uint32_t h = (uint32_t)((a >> 2) & HB_MASK);
        for (uint32_t j = hHead[h]; j != 0; j = hNext[j - 1]) {
            if (sCur[j - 1].addr == a) {
                float cv = sCur[j - 1].val;
                if (cv < pv) {
                    float ratio = 1.0f - cv / pv;
                    if (ratio >= DROP_MIN_RATIO && ratio <= DROP_MAX_RATIO) {
                        int found = -1;
                        for (int k = 0; k < g_candCount; k++) {
                            if (g_cands[k].addr == a && g_cands[k].zone == zone) { found = k; break; }
                        }
                        if (found >= 0) {
                            CandItem *c = &g_cands[found];
                            c->hitThis = 1; c->misses = 0;
                            c->lastVal = cv;
                            if (pv > c->peak) c->peak = pv;
                            c->hits++;
                        } else if (g_candCount < CAND_LIMIT) {
                            CandItem *c = &g_cands[g_candCount++];
                            c->addr = a; c->peak = pv; c->lastVal = cv;
                            c->hits = 1; c->misses = 0; c->hitThis = 1; c->zone = zone;
                            newCand++;
                        } else {
                            for (int r = 0; r < g_candCount; r++) {
                                if (g_cands[r].zone == zone && g_cands[r].hits <= 1 && g_cands[r].misses > 0) {
                                    CandItem *c = &g_cands[r];
                                    c->addr = a; c->peak = pv; c->lastVal = cv;
                                    c->hits = 1; c->misses = 0; c->hitThis = 1; c->zone = zone;
                                    newCand++;
                                    break;
                                }
                            }
                        }
                    }
                }
                break;
            }
        }
    }

    // 4. 压缩：本区未命中 → misses++（连续 2 次丢弃）；其他区不动
    int w = 0;
    for (int k = 0; k < g_candCount; k++) {
        if (g_cands[k].zone == zone && !g_cands[k].hitThis) {
            if (++g_cands[k].misses >= 2) continue;
        }
        g_cands[w++] = g_cands[k];
    }
    g_candCount = w;

    // 5. 实时写：hits>=2 = 本区连续 2 周期（~6.4s）持续掉血 = 活体 HP
    g_appliedLast = 0;
    if (g_godMode || g_oneHitKill) {
        task_t task = mach_task_self();
        int appliedLogs = 0;
        for (int k = 0; k < g_candCount && g_appliedLast < APPLY_PER_TICK; k++) {
            CandItem *c = &g_cands[k];
            if (c->hits < 2) continue;
            float curV = 0; vm_size_t sz = 0;
            if (vm_read_overwrite(task, c->addr, 4, (vm_address_t)&curV, &sz) == KERN_SUCCESS) {
                if (curV >= HP_MIN_VAL && curV <= HP_MAX_VAL) {
                    float wv = g_oneHitKill ? 0.0f : c->peak;
                    vm_write(task, c->addr, (vm_address_t)&wv, 4);
                    g_appliedLast++;
                    if (g_writtenCount < RECHECK_MAX) g_writtenLast[g_writtenCount++] = c->addr;
                    if (appliedLogs < 3) {
                        VGLog("[hit] 0x%llx %.1f -> %.1f (%s z%d)", (unsigned long long)c->addr, curV, wv,
                              g_oneHitKill ? "OHK" : "GOD", zone);
                        appliedLogs++;
                    }
                }
            }
        }
    }

    // 6. 状态行（8 轮 = 全区一遍 ≈ 3.2s 一条）
    g_tickCount++;
    if (g_tickCount % 8 == 0) {
        int hot = 0;
        for (int k = 0; k < g_candCount; k++) if (g_cands[k].hits >= 2) hot++;
        VGLog("[tick] z%d snap=%zu/%d cand=%d(hot %d,new %d) applied=%d mode=%s",
              zone, nCur, (int)MAX_SNAP_ITEMS, g_candCount, hot, newCand, g_appliedLast,
              g_oneHitKill ? "OHK" : (g_godMode ? "GOD" : "off"));
    }
}

static void VGScanTick(void) {
    static volatile int scanning = 0;
    if (__sync_lock_test_and_set(&scanning, 1)) return;

    int zone = g_curZone;
    // 槽交换：旧 cur → prev；新扫描写 cur
    SnapItem *tmp = g_snaps[zone][1];
    g_snaps[zone][1] = g_snaps[zone][0];
    g_snaps[zone][0] = tmp;
    g_snapCounts[zone][1] = g_snapCounts[zone][0];

    if (!g_snaps[zone][0]) g_snaps[zone][0] = malloc(sizeof(SnapItem) * MAX_SNAP_ITEMS);
    g_snapCounts[zone][0] = VGScanZone(zone, g_snaps[zone][0]);
    g_zoneFill[zone]++;

    if (g_zoneFill[zone] >= 2) {
        VGDifferentialZone(zone);
    }

    g_curZone = (zone + 1) % ZONES;
    scanning = 0;
}

#pragma mark - 变速（renderScene 有则 hook）

static void (*orig_renderScene)(id, SEL, id);
static void hooked_renderScene(id self, SEL _cmd, id link) {
    int extra = 0;
    if (g_speedMult >= 3.0f)      extra = 2;
    else if (g_speedMult >= 2.0f) extra = 1;
    orig_renderScene(self, _cmd, link);
    for (int i = 0; i < extra; i++) orig_renderScene(self, _cmd, link);
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
    if (g_panel && g_panel.superview) {
        [g_panel removeFromSuperview];
        g_panel = nil;
        return;
    }
    g_panel = nil;
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
        title.text = @"香草英雄团 v9";
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

        // v5 修复 R3：按钮状态同步自全局 flag（重开面板不再显示假“关”）
        UIButton *ohk = [UIButton buttonWithType:UIButtonTypeSystem];
        ohk.frame = CGRectMake(15, 56, 270, 52);
        [ohk setTitle:g_oneHitKill ? @"⚔️ 秒杀: 开" : @"⚔️ 秒杀: 关" forState:UIControlStateNormal];
        ohk.backgroundColor = g_oneHitKill ? [UIColor colorWithRed:0.85 green:0.1 blue:0.1 alpha:0.95]
                                            : [UIColor colorWithWhite:0.25 alpha:0.8];
        [ohk setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        ohk.titleLabel.font = [UIFont boldSystemFontOfSize:17];
        ohk.layer.cornerRadius = 12;
        [ohk addTarget:self action:@selector(vg_onOhk:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:ohk];

        UIButton *god = [UIButton buttonWithType:UIButtonTypeSystem];
        god.frame = CGRectMake(15, 118, 270, 52);
        [god setTitle:g_godMode ? @"🛡️ 无敌: 开" : @"🛡️ 无敌: 关" forState:UIControlStateNormal];
        god.backgroundColor = g_godMode ? [UIColor colorWithRed:0.1 green:0.6 blue:0.2 alpha:0.95]
                                         : [UIColor colorWithWhite:0.25 alpha:0.8];
        [god setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        god.titleLabel.font = [UIFont boldSystemFontOfSize:17];
        god.layer.cornerRadius = 12;
        [god addTarget:self action:@selector(vg_onGod:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:god];

        for (int i = 0; i < 3; i++) {
            UIButton *b = [UIButton buttonWithType:UIButtonTypeSystem];
            b.frame = CGRectMake(15 + i*95, 182, 88, 40);
            [b setTitle:[@[@"1x",@"2x",@"3x"] objectAtIndex:i] forState:UIControlStateNormal];
            NSArray *vals = @[@1.0f, @2.0f, @3.0f];
            float sv = [vals[i] floatValue];
            BOOL active = (fabsf(g_speedMult - sv) < 0.01f);
            b.backgroundColor = active ? [UIColor colorWithRed:0.2 green:0.5 blue:0.9 alpha:0.9]
                                       : [UIColor colorWithWhite:0.2 alpha:0.8];
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
        st.text = @"值域已收紧 [100,20000] 防扫描截断\n秒杀=清零 | 无敌=回峰值（互斥）\n同时开=写值冲突（敌我不可分），见日志 [tick]";
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
        VGLog("[init] VHCheat v9 loaded");

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
            VGLog("[init] cheat loop ready (%dms/zone, %d zones, zone revisit ~%.1fs)",
                  TICK_MS, ZONES, TICK_MS * ZONES / 1000.0);
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
