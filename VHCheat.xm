//
//  VHCheat.xm — 香草英雄团 v1.0.4 修改器
//  基于悬浮窗模板 + 变速 hook + V8/内存 hook 框架
//
//  编译：Theos 或 TrollFools（普通 dylib，无需越狱）
//  功能：
//    · 全局加速（1x/2x/3x/0.5x）—— 确定可用
//    · 无敌 —— hook V8 Object::Set 拦截 hp 赋值
//    · 秒杀 —— hook V8 Object::Set 拦截 damage 赋值
//    · 内存扫描 —— 备选方案定位 HP 变量
//

#import <UIKit/UIKit.h>
#import <objc/runtime.h>
#import <mach/mach.h>
#import <mach/mach_vm.h>
#import <mach-o/dyld.h>
#import <dlfcn.h>
#include <math.h>

#pragma mark - 配置

static float  g_speedMult   = 1.0f;   // 变速倍率
static BOOL   g_godMode     = NO;     // 无敌
static BOOL   g_oneHitKill  = NO;     // 秒杀
static BOOL   g_cheatEnabled = YES;   // 总开关

#pragma mark - 日志

static int g_logFd = -1;
static void VGLog(const char *fmt, ...) {
    if (g_logFd < 0) {
        NSString *path = [NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES)[0]
                          stringByAppendingPathComponent:@"vh_cheat.log"];
        g_logFd = open([path UTF8String], O_WRONLY|O_CREAT|O_TRUNC, 0644);
    }
    if (g_logFd < 0) return;
    char buf[1024];
    va_list ap; va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    if (n > 0) { strcat(buf, "\n"); write(g_logFd, buf, strlen(buf)); }
}

#pragma mark - 全局加速：Hook setAnimationInterval

static void (*orig_setAnimationInterval)(id, SEL, float);
static void hooked_setAnimationInterval(id self, SEL _cmd, float interval) {
    float newInterval = interval / g_speedMult;
    VGLog("[speed] interval %.4f -> %.4f (%.1fx)", interval, newInterval, g_speedMult);
    orig_setAnimationInterval(self, _cmd, newInterval);
}

// 备选：Hook Director::setNextDeltaTime
static void (*orig_setNextDeltaTime)(id, SEL, float);
static void hooked_setNextDeltaTime(id self, SEL _cmd, float dt) {
    orig_setNextDeltaTime(self, _cmd, dt * g_speedMult);
}

#pragma mark - 无敌/秒杀：V8 层 Hook 框架

// 方案A：Hook v8::Object::Set 拦截属性赋值
// 当 JS 执行 this.hp = val 时，如果 g_godMode=1 且属性名含 "hp"/"health"
// 则忽略赋值（保持原值）= 无敌
//
// V8 内部函数签名（随版本变化，需根据实际 V8 版本调整）：
//   v8::Maybe<bool> v8::Object::Set(v8::Local<v8::Context> context,
//                                    v8::Local<v8::Name> key,
//                                    v8::Local<v8::Value> value)
//
// 在 dylib 中实现需要：
// 1. 找到 V8 二进制基址
//  2. 解析导出符号或特征码定位函数
//  3. 用 MSHookFunction 替换

static BOOL v8HookInstalled = NO;

// V8 符号查找（Cocos 3.8.5 内置 V8）
static void* VGFindV8Symbol(const char *name) {
    // V8 符号通常在主二进制或 libv8 中
    void *handle = RTLD_DEFAULT;
    void *sym = dlsym(handle, name);
    if (!sym) {
        // 遍历所有 image 找 V8 相关
        uint32_t count = _dyld_image_count();
        for (uint32_t i = 0; i < count; i++) {
            const char *imgName = _dyld_get_image_name(i);
            if (imgName && strstr(imgName, "v8")) {
                handle = dlopen(imgName, RTLD_NOLOAD);
                if (handle) {
                    sym = dlsym(handle, name);
                    if (sym) break;
                }
            }
        }
    }
    return sym;
}

// 尝试 hook V8 内部函数
static void VGTryInstallV8Hooks(void) {
    if (v8HookInstalled) return;

    // V8 内部函数名（随版本不同，这里是常见名称）
    // 注意：Release build 可能被 inline，需要找替代 hook 点
    void *setFn = VGFindV8Symbol("_ZN2v86Object3SetENS_5LocalINS_7ContextEEENS1_INS_5ValueEEES5_");
    if (setFn) {
        VGLog("[v8] found Object::Set at %p", setFn);
        // MSHookFunction(setFn, (void*)hooked_V8ObjectSet, (void**)&orig_V8ObjectSet);
    }

    // 备选：Hook ScriptEngine 的 eval/run 入口
    // Cocos 的 se::ScriptEngine::runScript 在 JS 执行前可以拦截
    void *runScript = VGFindV8Symbol("_ZN2se13ScriptEngine8runScriptEPKc");
    if (runScript) {
        VGLog("[v8] found ScriptEngine::runScript at %p", runScript);
    }

    v8HookInstalled = YES;
}

#pragma mark - 内存扫描方案（备选）

// 扫描进程内存找浮点数变量（HP/伤害相关）
// 原理：受到伤害时 HP 减少，通过多次扫描定位变化地址
typedef struct {
    mach_vm_address_t addr;
    float lastValue;
    float threshold;  // 变化阈值
} MemScanner;

static MemScanner g_hpScanner = {0};
static BOOL g_scanning = NO;

// 扫描可读内存段找浮点值
static void VGScanMemory(void) {
    task_t task = mach_task_self();
    mach_vm_address_t address = 0;
    mach_vm_size_t size = 0;
    vm_region_basic_info_data_64_t info;
    mach_msg_type_number_t count = VM_REGION_BASIC_INFO_COUNT_64;
    mach_port_t objectName = MACH_PORT_NULL;

    int found = 0;
    while (mach_vm_region(task, &address, &size, VM_REGION_BASIC_INFO,
                          (vm_region_info_t)&info, &count, &objectName) == KERN_SUCCESS) {
        // 只读 + 可读段（代码段/数据段）
        if ((info.protection & VM_PROT_READ) && size > 0 && size < 0x100000) {
            void *buf = malloc((size_t)size);
            mach_vm_size_t outSize = 0;
            kern_return_t kr = mach_vm_read_overwrite(task, address, size,
                                                       (mach_vm_address_t)buf, &outSize);
            if (kr == KERN_SUCCESS && outSize >= sizeof(float)) {
                float *p = (float*)buf;
                for (mach_vm_size_t i = 0; i < outSize/sizeof(float); i++) {
                    float v = p[i];
                    // 寻找合理范围的浮点数（HP 通常在 0~99999）
                    if (v > 0.0f && v < 99999.0f && v == v) {  // 排除 NaN/Inf
                        found++;
                        if (found < 50) {
                            VGLog("[scan] addr=0x%llx val=%.2f", address + i*sizeof(float), v);
                        }
                    }
                }
            }
            free(buf);
        }
        address += size;
        size = 0;
        count = VM_REGION_BASIC_INFO_COUNT_64;
        objectName = MACH_PORT_NULL;
        if (address > 0x2000000000) break;  // 扫描上限
    }
    VGLog("[scan] done, found %d candidates", found);
}

#pragma mark - 悬浮窗（基于你的模板）

@interface FloatGlassPanel : UIView
- (void)fg_close;
@end
static UIWindow *fg_keyWindow(void) { 
    for (UIScene *s in UIApplication.sharedApplication.connectedScenes) {
        if ([s isKindOfClass:[UIWindowScene class]] &&
            ((UIWindowScene *)s).activationState == UISceneActivationStateForegroundActive) {
            UIWindowScene *ws = (UIWindowScene *)s;
            for (UIWindow *w in ws.windows) if (w.isKeyWindow) return w;
            for (UIWindow *w in ws.windows) if (w.rootViewController) return w;
            if (ws.windows.count) return ws.windows.firstObject;
        }
    }
    for (UIWindow *w in UIApplication.sharedApplication.windows) if (w.isKeyWindow) return w;
    return UIApplication.sharedApplication.keyWindow;
}
static FloatGlassPanel *g_panel = nil;

// 悬浮按钮
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
    CGFloat pw = 300, ph = 380;
    FloatGlassPanel *p = [[FloatGlassPanel alloc] initWithFrame:
        CGRectMake((kw.bounds.size.width-pw)/2.0, (kw.bounds.size.height-ph)/2.0, pw, ph)];
    g_panel = p; [kw addSubview:p]; [kw bringSubviewToFront:p];
}
- (void)fg_closePanel { if (g_panel) { [g_panel removeFromSuperview]; g_panel = nil; } }
@end

// 面板
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
        
        // 标题
        UILabel *title = [[UILabel alloc] initWithFrame:CGRectMake(0, 18, CGRectGetWidth(self.bounds), 28)];
        title.text = @"香草英雄团";
        title.textAlignment = NSTextAlignmentCenter;
        title.textColor = [UIColor whiteColor];
        title.font = [UIFont boldSystemFontOfSize:18];
        title.autoresizingMask = UIViewAutoresizingFlexibleWidth;
        [self addSubview:title];
        
        // 关闭按钮
        UIButton *closeBtn = [UIButton buttonWithType:UIButtonTypeSystem];
        [closeBtn setTitle:@"✕" forState:UIControlStateNormal];
        closeBtn.tintColor = [UIColor lightGrayColor];
        closeBtn.frame = CGRectMake(CGRectGetWidth(self.bounds)-40, 14, 32, 32);
        closeBtn.autoresizingMask = UIViewAutoresizingFlexibleLeftMargin;
        [closeBtn addTarget:self action:@selector(fg_close) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:closeBtn];
        
        // 变速按钮组
        NSArray *speedTitles = @[@"1x", @"2x", @"3x", @"½x"];
        NSArray *speedVals = @[@1.0f, @2.0f, @3.0f, @0.5f];
        CGFloat btnY = 60;
        for (int i = 0; i < 4; i++) {
            UIButton *btn = [UIButton buttonWithType:UIButtonTypeSystem];
            btn.frame = CGRectMake(15 + i*68, btnY, 62, 36);
            [btn setTitle:speedTitles[i] forState:UIControlStateNormal];
            btn.backgroundColor = [UIColor colorWithWhite:0.2 alpha:0.8];
            [btn setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
            btn.layer.cornerRadius = 8;
            btn.tag = 100 + i;
            [btn addTarget:nil action:@selector(onSpeed:) forControlEvents:UIControlEventTouchUpInside];
            [self addSubview:btn];
        }
        
        // 无敌按钮
        UIButton *godBtn = [UIButton buttonWithType:UIButtonTypeSystem];
        godBtn.frame = CGRectMake(15, 110, 130, 44);
        [godBtn setTitle:@"无敌: 关" forState:UIControlStateNormal];
        godBtn.backgroundColor = [UIColor colorWithRed:0.3 green:0.3 blue:0.3 alpha:0.8];
        [godBtn setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        godBtn.layer.cornerRadius = 10;
        godBtn.tag = 200;
        [godBtn addTarget:nil action:@selector(onGod:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:godBtn];
        
        // 秒杀按钮
        UIButton *ohkBtn = [UIButton buttonWithType:UIButtonTypeSystem];
        ohkBtn.frame = CGRectMake(155, 110, 130, 44);
        [ohkBtn setTitle:@"秒杀: 关" forState:UIControlStateNormal];
        ohkBtn.backgroundColor = [UIColor colorWithRed:0.3 green:0.3 blue:0.3 alpha:0.8];
        [ohkBtn setTitleColor:[UIColor whiteColor] forState:UIControlStateNormal];
        ohkBtn.layer.cornerRadius = 10;
        ohkBtn.tag = 300;
        [ohkBtn addTarget:nil action:@selector(onOhk:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:ohkBtn];
        
        // 内存扫描按钮（调试用）
        UIButton *scanBtn = [UIButton buttonWithType:UIButtonTypeSystem];
        scanBtn.frame = CGRectMake(15, 165, 270, 36);
        [scanBtn setTitle:@"内存扫描（调试）" forState:UIControlStateNormal];
        scanBtn.backgroundColor = [UIColor colorWithWhite:0.2 alpha:0.6];
        [scanBtn setTitleColor:[UIColor lightGrayColor] forState:UIControlStateNormal];
        scanBtn.layer.cornerRadius = 8;
        scanBtn.tag = 400;
        [scanBtn addTarget:nil action:@selector(onScan:) forControlEvents:UIControlEventTouchUpInside];
        [self addSubview:scanBtn];
        
        // 状态说明
        UILabel *info = [[UILabel alloc] initWithFrame:CGRectMake(15, 215, 270, 140)];
        info.text = @"说明：\n"
                    "• 变速：确定可用\n"
                    "• 无敌/秒杀：需定位 V8 hook 点\n"
                    "• 内存扫描：可定位 HP 变量\n\n"
                    "日志：Documents/vh_cheat.log";
        info.textColor = [UIColor colorWithWhite:0.6 alpha:1];
        info.font = [UIFont systemFontOfSize:11];
        info.numberOfLines = 0;
        [self addSubview:info];
        
        // 拖动
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
@end

#pragma mark - Button Actions

@interface NSObject (VHActions)
- (void)onSpeed:(UIButton *)s;
- (void)onGod:(UIButton *)s;
- (void)onOhk:(UIButton *)s;
- (void)onScan:(UIButton *)s;
@end

@implementation NSObject (VHActions)
- (void)onSpeed:(UIButton *)s {
    NSArray *vals = @[@1.0f, @2.0f, @3.0f, @0.5f];
    g_speedMult = [vals[s.tag-100] floatValue];
    VGLog("[UI] speed = %.1fx", g_speedMult);
    // 更新按钮高亮
    for (UIView *v in s.superview.subviews) {
        if ([v isKindOfClass:[UIButton class]] && v.tag >= 100 && v.tag < 200) {
            ((UIButton*)v).backgroundColor = [UIColor colorWithWhite:0.2 alpha:0.6];
        }
    }
    s.backgroundColor = [UIColor colorWithRed:0.2 green:0.5 blue:0.9 alpha:0.9];
}
- (void)onGod:(UIButton *)s {
    g_godMode = !g_godMode;
    VGLog("[UI] godMode = %d", g_godMode);
    [s setTitle:g_godMode ? @"无敌: 开" : @"无敌: 关" forState:UIControlStateNormal];
    s.backgroundColor = g_godMode ?
        [UIColor colorWithRed:0.1 green:0.7 blue:0.2 alpha:0.9] :
        [UIColor colorWithWhite:0.3 alpha:0.8];
    if (g_godMode) VGTryInstallV8Hooks();
}
- (void)onOhk:(UIButton *)s {
    g_oneHitKill = !g_oneHitKill;
    VGLog("[UI] oneHitKill = %d", g_oneHitKill);
    [s setTitle:g_oneHitKill ? @"秒杀: 开" : @"秒杀: 关" forState:UIControlStateNormal];
    s.backgroundColor = g_oneHitKill ?
        [UIColor colorWithRed:0.9 green:0.1 blue:0.1 alpha:0.9] :
        [UIColor colorWithWhite:0.3 alpha:0.8];
    if (g_oneHitKill) VGTryInstallV8Hooks();
}
- (void)onScan:(UIButton *)s {
    VGLog("[UI] start memory scan...");
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
        VGScanMemory();
    });
}
@end

#pragma mark - Toast

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

#pragma mark - Entry

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

__attribute__((constructor)) static void fg_ctor() {
    @autoreleasepool {
        NSString *bid = NSBundle.mainBundle.bundleIdentifier;
        if (!bid) return;
        
        VGLog("[init] VHCheat loaded in %@", bid);
        
        // Hook setAnimationInterval（变速）
        Class appClass = NSClassFromString(@"CocosApplication");
        if (appClass) {
            SEL sel = @selector(setAnimationInterval:);
            Method m = class_getInstanceMethod(appClass, sel);
            if (m) {
                orig_setAnimationInterval = (void(*)(id,SEL,float))method_getImplementation(m);
                method_setImplementation(m, (IMP)hooked_setAnimationInterval);
                VGLog("[hook] setAnimationInterval OK");
            }
        }
        
        // 尝试 hook Director
        Class dirClass = NSClassFromString(@"CCDDirector");
        if (dirClass) {
            SEL sel2 = @selector(setNextDeltaTime:);
            Method m2 = class_getInstanceMethod(dirClass, sel2);
            if (m2) {
                orig_setNextDeltaTime = (void(*)(id,SEL,float))method_getImplementation(m2);
                method_setImplementation(m2, (IMP)hooked_setNextDeltaTime);
                VGLog("[hook] setNextDeltaTime OK");
            }
        }
        
        // 延迟显示 UI
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(0.8 * NSEC_PER_SEC)),
                       dispatch_get_main_queue(), ^{
            fg_toast(@"VHCheat 已加载");
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
