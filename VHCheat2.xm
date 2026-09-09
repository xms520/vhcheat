//
//  VHCheat2.xm — 香草英雄团 v1.0.4 修改器 v2
//  ─────────────────────────────────────────────────────────────────────
//  v1 失败根因（日志实锤）：
//    1. NSClassFromString(@"CocosApplication") = nil —— 它是 C++ 类（cc::CocosApplication），
//       ObjC runtime 里根本没有 → setAnimationInterval hook 全落空（日志无 OK 行）
//    2. 内存扫描 found 6000万 = 裸扫全内存没过滤 + V8 里 HP 是 HeapNumber（带 tag），
//       裸 float 扫描找不到
//    3. 日志 "loaded in @" = NSBundle.mainBundle.bundleIdentifier 在 constructor 里为空
//       （constructor 执行时 main bundle 未初始化完毕）——但 dylib 确实加载了
//
//  v2 正确锚点（来自二进制静态分析）：
//    · 游戏主 VC = ObjC 类 "ViewController"（__objc_classname 实锤）
//      - (id)initWithApp:(cc::Application*)app fps:(float)fps
//      - (void)renderScene:(CADisplayLink*)link   ← CADisplayLink 每帧回调！
//    · CocosApplication/AppDelegate/AppDelegateBridge 都是 ObjC 可见的
//    · setPreferredFramesPerSecond: selector 存在
//
//  功能实现：
//    · 全局加速：hook renderScene: 每帧多调 orig N 次（N=1.0/1.5/2/3 倍率）
//      ⚠️ 物理可能不稳定，但本游戏是卡牌/塔防类，帧重复积分风险低
//    · 秒杀/无敌：renderScene: hook 内按间隔做「V8 堆数值锁定」
//      方案 A：扫描 writable 内存找特定数值模式的浮点/双精度 → 写极值
//      方案 B（更稳）：把扫描结果打日志，先收集数据再精准打（诊断模式）
//
//  使用：
//    · 面板按钮：1x / 2x / 3x + 无敌 + 秒杀 + 诊断扫描
//    · 日志：Documents/vh_cheat.log
//

#import <UIKit/UIKit.h>
#import <objc/runtime.h>
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

static float  g_speedMult   = 1.0f;   // 变速倍率（1.0 = 正常）
static BOOL   g_godMode     = NO;     // 无敌
static BOOL   g_oneHitKill  = NO;     // 秒杀
static BOOL   g_diagScan    = NO;     // 诊断扫描（dump 内存值分布，不写）
static float  g_lastScan    = 0;      // 上次扫描时间

// 前向声明（定义在后面）
static void VGDoCheatScan(void);
static void VGRunDiagScan(void);

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

#pragma mark - Hook: ViewController renderScene: （帧驱动 = 变速 + 秒杀回调）

static void (*orig_renderScene)(id, SEL, id);
static BOOL  g_hookInstalled = NO;
static int   g_frameCount   = 0;

static void hooked_renderScene(id self, SEL _cmd, id link) {
    // 变速：多调 orig N 次（N 由倍率决定）
    int extraCalls = 0;
    if (g_speedMult >= 3.0f)      extraCalls = 2;   // 3x = 1+2
    else if (g_speedMult >= 2.0f) extraCalls = 1;   // 2x = 1+1
    else if (g_speedMult >= 1.5f) extraCalls = 0;  // 1.5x = 帧间隔跳帧（下面处理）

    orig_renderScene(self, _cmd, link);
    for (int i = 0; i < extraCalls; i++) {
        orig_renderScene(self, _cmd, link);
    }

    // 1.5x 特殊处理：每 2 帧多跑 1 帧 = 1.5x
    if (g_speedMult >= 1.5f && g_speedMult < 2.0f) {
        g_frameCount++;
        if (g_frameCount % 2 == 0) {
            orig_renderScene(self, _cmd, link);
        }
    }

    // 秒杀/无敌/诊断：每 500ms 扫一次内存（在帧回调里做节流，不起线程）
    static double lastAction = 0;
    double now = CFAbsoluteTimeGetCurrent();
    if (now - lastAction > 0.5 && (g_godMode || g_oneHitKill || g_diagScan)) {
        lastAction = now;
        VGDoCheatScan();
    }
}

#pragma mark - 安装 Hook（等 ViewController 类出现）

static void VGInstallHooks(void) {
    if (g_hookInstalled) return;

    // 游戏主 VC（二进制 __objc_classname 实锤：类名就是 "ViewController"）
    Class vcClass = NSClassFromString(@"ViewController");
    if (!vcClass) {
        // 类还没注册（dylib constructor 太早）—— 注册回调稍后重试
        return;
    }
    SEL sel = sel_registerName("renderScene:");
    Method m = class_getInstanceMethod(vcClass, sel);
    if (!m) {
        VGLog("[hook] ViewController has NO renderScene: method (列出方法看日志)");
        // 诊断：dump 该类全部方法名
        unsigned int n = 0;
        Method *list = class_copyMethodList(vcClass, &n);
        NSMutableString *ms = [NSMutableString stringWithString:@"[hook] VC methods: "];
        for (unsigned int i = 0; i < n; i++) {
            [ms appendFormat:@"%@ ", NSStringFromSelector(method_getName(list[i]))];
        }
        VGLog("%s", [ms UTF8String]);
        free(list);
        g_hookInstalled = YES; // 只试一次，别刷日志
        return;
    }

    orig_renderScene = (void(*)(id,SEL,id))method_getImplementation(m);
    method_setImplementation(m, (IMP)hooked_renderScene);
    g_hookInstalled = YES;
    VGLog("[hook] ViewController.renderScene: OK ← 帧驱动已拦截");
}

// 每秒检查一次类是否可用（constructor 时类未注册）
static void VGTryHookLoop(void) {
    __block int tries = 0;
    dispatch_async(dispatch_get_main_queue(), ^{
        void (^tick)(void) = ^{
            if (g_hookInstalled) return;
            VGInstallHooks();
            if (!g_hookInstalled && ++tries < 60) {
                dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(1.0 * NSEC_PER_SEC)),
                               dispatch_get_main_queue(), tick);
            } else if (!g_hookInstalled) {
                VGLog("[hook] 放弃：60 秒内 ViewController/renderScene: 未出现");
            }
        };
        tick();
    });
}

#pragma mark - V8 堆数值扫描/锁定（秒杀/无敌核心）

// V8 堆里 JS number 的存储形式：
//   Smi:  31bit 整数直接存指针低位（值<<1 | 0），不占内存对象
//   HeapNumber: 8 字节 IEEE double，地址低位 tag = 1（指针|1）
// → 数值本身是 4 字节对齐的 double/float！扫内存可命中
//
// 本游戏（香草英雄团）：塔防/卡牌类，HP 大概率 1~9999999 的整数或浮点
//
// 策略（保守——先诊断再动手）：
//   秒杀模式：扫描所有可写内存中数值在 [1, 9999999] 的 float32，
//            与上一轮快照对比「变小的值」= 受击掉血的 HP → 写 0
//   无敌模式：「变小的值」→ 写回旧值
//
// ⚠️ 误伤风险：数值过滤靠变化方向 + 范围。面板提供诊断按钮先看分布

typedef struct { uint64_t addr; float val; } SnapItem;
static SnapItem *g_snapA = NULL;
static SnapItem *g_snapB = NULL;
static size_t    g_snapCountA = 0, g_snapCountB = 0;
static BOOL      g_haveSnapA = NO, g_haveSnapB = NO;
static int       g_snapSeq = 0;   // 0=A 1=B 交替

// 快照上限：最多 200 万个候选（内存足够）
#define MAX_SNAP_ITEMS (2000000)

static BOOL VGIsWritableRegion(vm_region_basic_info_data_64_t *info) {
    return (info->protection & VM_PROT_WRITE) &&
           (info->protection & VM_PROT_READ) &&
          !(info->share_mode == SM_TRUESHARED);  // 跳过共享库段
}

// 采集快照：所有 writable 区域内 [1, 9999999] 的 float32
static size_t VGTakeSnapshot(SnapItem **outBuf) {
    if (!*outBuf) *outBuf = malloc(sizeof(SnapItem) * MAX_SNAP_ITEMS);
    size_t count = 0;
    task_t task = mach_task_self();

    vm_address_t address = 0x0;
    vm_size_t size = 0;
    vm_region_basic_info_data_64_t info;
    mach_msg_type_number_t countInfo = VM_REGION_BASIC_INFO_COUNT_64;
    mach_port_t objectName = MACH_PORT_NULL;

    while (count < MAX_SNAP_ITEMS - 4096) {
        kern_return_t kr = vm_region_64(task, &address, &size, VM_REGION_BASIC_INFO,
                                        (vm_region_info_t)&info, &countInfo, &objectName);
        if (kr != KERN_SUCCESS) break;
        if (address > 0x800000000) break;  // 越界保护

        if (VGIsWritableRegion(&info) && size >= 64) {
            // 分块读（防超大段一次性失败）
            vm_address_t cur = address;
            vm_size_t remain = size;
            while (remain > 0 && count < MAX_SNAP_ITEMS - 4096) {
                vm_size_t chunk = remain > (4 << 20) ? (4 << 20) : remain;
                void *buf = malloc((size_t)chunk);
                if (buf) {
                    vm_size_t outSize = 0;
                    if (vm_read_overwrite(task, cur, chunk, (vm_address_t)buf, &outSize) == KERN_SUCCESS && outSize == chunk) {
                        size_t nfloat = chunk / 4;
                        float *f = (float*)buf;
                        for (size_t i = 0; i < nfloat && count < MAX_SNAP_ITEMS; i++) {
                            float v = f[i];
                            if (v >= 1.0f && v <= 9999999.0f) {
                                (*outBuf)[count].addr = (uint64_t)(cur + i * 4);
                                (*outBuf)[count].val = v;
                                count++;
                            }
                        }
                    }
                    free(buf);
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

// 对比 A/B 快照：找出「值变小」的地址（受击掉血特征）
// 返回命中数，写入 result 数组（addr + oldVal + newVal）
typedef struct { uint64_t addr; float oldVal; float newVal; } DeltaItem;
static DeltaItem g_deltas[8192];

static int VGDiffSnapshots(void) {
    if (!g_haveSnapA || !g_haveSnapB) return 0;
    int hits = 0;
    // hash 索引 B 快照地址（简化：线性对撞——B 排序 + 二分）
    // B 不排序，用简单 hash 桶
    #define HB_SIZE (1<<20)
    #define HB_MASK (HB_SIZE-1)
    static uint32_t *hHead = NULL;   // 桶头（g_snapB 下标+1，0=空）
    static uint32_t *hNext = NULL;   // 链表 next
    if (!hHead) hHead = calloc(HB_SIZE, sizeof(uint32_t));
    if (!hNext) hNext = calloc(MAX_SNAP_ITEMS, sizeof(uint32_t));
    memset(hHead, 0, HB_SIZE * sizeof(uint32_t));

    for (uint32_t i = 0; i < g_snapCountB; i++) {
        uint32_t h = (uint32_t)((g_snapB[i].addr >> 2) & HB_MASK);
        hNext[i] = hHead[h];
        hHead[h] = i + 1;
    }
    for (uint32_t i = 0; i < g_snapCountA && hits < 8192; i++) {
        uint64_t a = g_snapA[i].addr;
        uint32_t h = (uint32_t)((a >> 2) & HB_MASK);
        for (uint32_t j = hHead[h]; j != 0; j = hNext[j-1]) {
            if (g_snapB[j-1].addr == a) {
                float oldV = g_snapA[i].val, newV = g_snapB[j-1].val;
                // 数值下降且两值都在合理 HP 范围 → 掉血特征
                if (newV < oldV && oldV <= 9999999.0f && newV >= 0.0f &&
                    (oldV - newV) >= 1.0f) {
                    g_deltas[hits].addr = a;
                    g_deltas[hits].oldVal = oldV;
                    g_deltas[hits].newVal = newV;
                    hits++;
                }
                break;
            }
        }
    }
    return hits;
}

// 秒杀/无敌执行：对「上一轮发现的掉血地址」持续操作
static uint64_t g_lockAddrs[256];
static float   g_lockBase[256];
static int      g_lockCount = 0;

static void VGDoCheatScan(void) {
    // 轮转快照
    SnapItem **cur = (g_snapSeq == 0) ? &g_snapB : &g_snapA;
    size_t cnt = VGTakeSnapshot(cur);
    if (g_snapSeq == 0) { g_snapCountB = cnt; g_haveSnapB = YES; }
    else                { g_snapCountA = cnt; g_haveSnapA = YES; }
    g_snapSeq ^= 1;

    if (g_haveSnapA && g_haveSnapB) {
        int hits = VGDiffSnapshots();
        if (hits > 0) {
            // 诊断模式：打印前 30 条掉血记录
            if (g_diagScan) {
                for (int i = 0; i < hits && i < 30; i++) {
                    VGLog("[diag] drop addr=0x%llx %.1f -> %.1f",
                          (unsigned long long)g_deltas[i].addr,
                          g_deltas[i].oldVal, g_deltas[i].newVal);
                }
            }
            // 记录锁定目标（秒杀=写0；无敌=写回旧值）
            g_lockCount = 0;
            for (int i = 0; i < hits && g_lockCount < 256; i++) {
                // 过滤明显噪音：下降超过 90% 且旧值 > 100 的可能是伤害值本身，跳过
                float ratio = g_deltas[i].newVal / g_deltas[i].oldVal;
                BOOL plausibleHP = (g_deltas[i].oldVal >= 5.0f) && (ratio > 0.01f);
                if (plausibleHP) {
                    g_lockAddrs[g_lockCount] = g_deltas[i].addr;
                    g_lockBase[g_lockCount]  = g_deltas[i].oldVal;
                    g_lockCount++;
                }
            }
            if (g_lockCount > 0) {
                VGLog("[cheat] lock targets=%d (god=%d ohk=%d)",
                      g_lockCount, g_godMode, g_oneHitKill);
            }
        }

        // 应用锁定（每 500ms）
        if (g_lockCount > 0 && (g_godMode || g_oneHitKill)) {
            task_t task = mach_task_self();
            int applied = 0;
            for (int i = 0; i < g_lockCount; i++) {
                float w = g_godMode ? g_lockBase[i] : 0.0f;  // 无敌=回满,秒杀=清零
                if (g_oneHitKill && !g_godMode) w = 0.0f;
                if (g_oneHitKill && g_godMode)  w = 0.0f;    // 同时开以秒杀优先
                vm_size_t sz = 0;
                float cur = 0;
                if (vm_read_overwrite(task, g_lockAddrs[i], 4, (vm_address_t)&cur, &sz) == KERN_SUCCESS) {
                    // 只动仍在合理范围的地址（防对象释放后复用误写）
                    if (cur >= 0.0f && cur <= 9999999.0f) {
                        vm_write(task, g_lockAddrs[i], (vm_address_t)&w, 4);
                        applied++;
                    }
                }
            }
            if (applied) VGLog("[cheat] applied=%d mode=%s", applied,
                               g_godMode ? "GOD" : "OHK");
        }
    }
}

#pragma mark - 诊断单次扫描（面板按钮）

static void VGRunDiagScan(void) {
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
        size_t cntA = VGTakeSnapshot(&g_snapA);
        g_snapCountA = cntA; g_haveSnapA = YES; g_snapSeq = 1;
        VGLog("[diag] snapshot A: %zu candidates in [1,9999999]", cntA);
        // 3 秒后第二张，自动找掉血
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 3 * NSEC_PER_SEC),
                       dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
            size_t cntB = VGTakeSnapshot(&g_snapB);
            g_snapCountB = cntB; g_haveSnapB = YES; g_snapSeq = 0;
            int hits = VGDiffSnapshots();
            VGLog("[diag] snapshot B: %zu, drops=%d", cntB, hits);
            for (int i = 0; i < hits && i < 50; i++) {
                VGLog("[diag] drop addr=0x%llx %.1f -> %.1f",
                      (unsigned long long)g_deltas[i].addr,
                      g_deltas[i].oldVal, g_deltas[i].newVal);
            }
        });
    });
}

#pragma mark - 悬浮窗 UI（保留 v1 模板样式）

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
        CABasicAnimation *breathe = [CABasicAnimation animationWithKeyPath:@"opacity"];
        breathe.fromValue = @0.6; breathe.toValue = @0.95; breathe.duration = 2.6;
        breathe.autoreverses = YES; breathe.repeatCount = HUGE_VALF;
        [sheen addAnimation:breathe forKey:@"fg_breathe"];
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
        CGFloat hw = self.frame.size.width/2.0, hh = self.frame.size.height/2.0;
        c.x = MAX(hw, MIN(c.x, sv.bounds.size.width - hw));
        c.y = MAX(hh, MIN(c.y, sv.bounds.size.height - hh));
        self.center = c; [g setTranslation:CGPointZero inView:sv];
    } else if (g.state == UIGestureRecognizerStateEnded) {
        CGFloat W = sv.bounds.size.width; CGPoint c = self.center;
        CGFloat m = self.frame.size.width/2.0 + 8.0;
        c.x = (c.x < W/2.0) ? m : (W - m);
        [UIView animateWithDuration:0.25 animations:^{ self.center = c; }];
    }
}
- (void)fg_tap:(UITapGestureRecognizer *)g { [self fg_togglePanel]; }
- (void)fg_togglePanel {
    if (g_panel) { [self fg_closePanel]; return; }
    UIWindow *kw = fg_keyWindow(); if (!kw) return;
    CGFloat pw = 300, ph = 400;
    FloatGlassPanel *p = [[FloatGlassPanel alloc] initWithFrame:
        CGRectMake((kw.bounds.size.width-pw)/2.0, (kw.bounds.size.height-ph)/2.0, pw, ph)];
    g_panel = p; [kw addSubview:p]; [kw bringSubviewToFront:p];
}
- (void)fg_closePanel { if (g_panel) { [g_panel removeFromSuperview]; g_panel = nil; } }
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

        UILabel *title = [[UILabel alloc] initWithFrame:CGRectMake(0, 18, CGRectGetWidth(self.bounds), 28)];
        title.text = @"香草英雄团 v2";
        title.textAlignment = NSTextAlignmentCenter;
        title.textColor = [UIColor whiteColor];
        title.font = [UIFont boldSystemFontOfSize:18];
        title.autoresizingMask = UIViewAutoresizingFlexibleWidth;
        [self addSubview:title];

        UIButton *closeBtn = [UIButton buttonWithType:UIButtonTypeSystem];
        [closeBtn setTitle:@"✕" forState:UIControlStateNormal];
        closeBtn.tintColor = [UIColor lightGrayColor];
        closeBtn.frame = CGRectMake(CGRectGetWidth(self.bounds)-40, 14, 32, 32);
        closeBtn.autoresizingMask = UIViewAutoresizingFlexibleLeftMargin;
        [closeBtn addTarget:self action:@selector(fg_close) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:closeBtn];

        // 变速按钮组（1x/2x/3x）
        NSArray *speedTitles = @[@"1x", @"2x", @"3x"];
        NSArray *speedVals = @[@1.0f, @2.0f, @3.0f];
        for (int i = 0; i < 3; i++) {
            UIButton *btn = [UIButton buttonWithType:UIButtonTypeSystem];
            btn.frame = CGRectMake(15 + i*95, 60, 88, 40);
            [btn setTitle:speedTitles[i] forState:UIControlStateNormal];
            btn.backgroundColor = (i == 0) ? [UIColor colorWithRed:0.2 green:0.5 blue:0.9 alpha:0.9]
                                          : [UIColor colorWithWhite:0.2 alpha:0.8];
            [btn setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
            btn.layer.cornerRadius = 10;
            btn.tag = 100 + i;
            [btn addTarget:self action:@selector(vg_onSpeed:) forControlEvents:UIControlEventTouchUpInside];
            [self addSubview:btn];
        }

        // 无敌
        UIButton *godBtn = [UIButton buttonWithType:UIButtonTypeSystem];
        godBtn.frame = CGRectMake(15, 115, 130, 44);
        [godBtn setTitle:@"无敌: 关" forState:UIControlStateNormal];
        godBtn.backgroundColor = [UIColor colorWithWhite:0.25 alpha:0.8];
        [godBtn setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        godBtn.layer.cornerRadius = 10;
        godBtn.tag = 200;
        [godBtn addTarget:self action:@selector(vg_onGod:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:godBtn];

        // 秒杀
        UIButton *ohkBtn = [UIButton buttonWithType:UIButtonTypeSystem];
        ohkBtn.frame = CGRectMake(155, 115, 130, 44);
        [ohkBtn setTitle:@"秒杀: 关" forState:UIControlStateNormal];
        ohkBtn.backgroundColor = [UIColor colorWithWhite:0.25 alpha:0.8];
        [ohkBtn setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        ohkBtn.layer.cornerRadius = 10;
        ohkBtn.tag = 300;
        [ohkBtn addTarget:self action:@selector(vg_onOhk:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:ohkBtn];

        // 诊断扫描
        UIButton *diagBtn = [UIButton buttonWithType:UIButtonTypeSystem];
        diagBtn.frame = CGRectMake(15, 170, 270, 36);
        [diagBtn setTitle:@"诊断扫描（先跑这个）" forState:UIControlStateNormal];
        diagBtn.backgroundColor = [UIColor colorWithWhite:0.2 alpha:0.6];
        [diagBtn setTitleColor:[UIColor lightGrayColor] forState:UIControlStateNormal];
        diagBtn.layer.cornerRadius = 8;
        [diagBtn addTarget:self action:@selector(vg_onDiag:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:diagBtn];

        // 说明
        UILabel *info = [[UILabel alloc] initWithFrame:CGRectMake(15, 218, 270, 165)];
        info.text = @"使用顺序：\n"
                    "1. 进战斗，先点「诊断扫描」\n"
                    "2. 等 3 秒（期间打个怪）\n"
                    "3. 把 vh_cheat.log 发我分析\n"
                    "4. 确认掉血地址后再开无敌/秒杀\n\n"
                    "变速即时生效；扫描每 0.5s 自动跑\n"
                    "日志: Documents/vh_cheat.log";
        info.textColor = [UIColor colorWithWhite:0.62 alpha:1];
        info.font = [UIFont systemFontOfSize:11];
        info.numberOfLines = 0;
        [self addSubview:info];

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
        CGFloat hw = self.frame.size.width/2.0, hh = self.frame.size.height/2.0;
        c.x = MAX(hw, MIN(c.x, sv.bounds.size.width - hw));
        c.y = MAX(hh, MIN(c.y, sv.bounds.size.height - hh));
        self.center = c; [g setTranslation:CGPointZero inView:sv];
    }
}

// 按钮响应（在 Panel 类内实现，target=self 正确）
- (void)vg_onSpeed:(UIButton *)s {
    NSArray *vals = @[@1.0f, @2.0f, @3.0f];
    g_speedMult = [vals[s.tag-100] floatValue];
    VGLog("[UI] speed = %.1fx", g_speedMult);
    for (UIView *v in self.subviews) {
        if ([v isKindOfClass:[UIButton class]] && v.tag >= 100 && v.tag < 200) {
            ((UIButton*)v).backgroundColor = [UIColor colorWithWhite:0.2 alpha:0.8];
        }
    }
    s.backgroundColor = [UIColor colorWithRed:0.2 green:0.5 blue:0.9 alpha:0.9];
}
- (void)vg_onGod:(UIButton *)s {
    g_godMode = !g_godMode;
    VGLog("[UI] godMode = %d", g_godMode);
    [s setTitle:g_godMode ? @"无敌: 开" : @"无敌: 关" forState:UIControlStateNormal];
    s.backgroundColor = g_godMode ?
        [UIColor colorWithRed:0.1 green:0.7 blue:0.2 alpha:0.9] :
        [UIColor colorWithWhite:0.25 alpha:0.8];
}
- (void)vg_onOhk:(UIButton *)s {
    g_oneHitKill = !g_oneHitKill;
    VGLog("[UI] oneHitKill = %d", g_oneHitKill);
    [s setTitle:g_oneHitKill ? @"秒杀: 开" : @"秒杀: 关" forState:UIControlStateNormal];
    s.backgroundColor = g_oneHitKill ?
        [UIColor colorWithRed:0.9 green:0.1 blue:0.1 alpha:0.9] :
        [UIColor colorWithWhite:0.25 alpha:0.8];
}
- (void)vg_onDiag:(UIButton *)s {
    VGLog("[UI] diag scan start");
    g_diagScan = YES;
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
        VGRunDiagScan();
    });
}
@end

#pragma mark - 工具

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

static void fg_toast(NSString *msg) {
    UIWindow *kw = fg_keyWindow(); if (!kw) return;
    UILabel *lab = [[UILabel alloc] init];
    lab.text = msg;
    lab.textColor = [UIColor whiteColor];
    lab.font = [UIFont systemFontOfSize:13];
    lab.textAlignment = NSTextAlignmentCenter;
    lab.backgroundColor = [UIColor colorWithWhite:0.0 alpha:0.72];
    lab.layer.cornerRadius = 10;
    lab.clipsToBounds = YES;
    [lab sizeToFit];
    CGFloat w = MIN(lab.frame.size.width + 28, kw.bounds.size.width - 40);
    CGFloat h = lab.frame.size.height + 16;
    lab.frame = CGRectMake((kw.bounds.size.width - w) / 2.0, kw.bounds.size.height - 110, w, h);
    [kw addSubview:lab]; [kw bringSubviewToFront:lab];
    [UIView animateWithDuration:0.35 delay:2.0 options:0 animations:^{ lab.alpha = 0; }
                     completion:^(BOOL f) { [lab removeFromSuperview]; }];
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

#pragma mark - 入口

__attribute__((constructor)) static void vg_ctor() {
    @autoreleasepool {
        // 延迟取 bundle id（constructor 里 mainBundle 未就绪，v1 的 bug）
        VGLog("[init] VHCheat v2 loaded");

        // 安装 renderScene: hook（延迟循环等类注册）
        VGTryHookLoop();

        // App 启动后挂 UI
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(1.5 * NSEC_PER_SEC)),
                       dispatch_get_main_queue(), ^{
            NSString *bid = NSBundle.mainBundle.bundleIdentifier ?: @"unknown";
            VGLog("[init] bundle=%@", bid);
            fg_toast(@"VHCheat v2 已加载");
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
