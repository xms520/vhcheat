TARGET := iphone:clang:latest:14.0
INSTALL_TARGET_PROCESSES = xp-mobile

include $(THEOS)/makefiles/common.mk

TWEAK_NAME = VHCheat

VHCheat_FILES = VHCheat.xm
VHCheat_CFLAGS = -fobjc-arc
VHCheat_FRAMEWORKS = UIKit Foundation
VHCheat_PRIVATE_FRAMEWORKS =

include $(THEOS_MAKE_PATH)/tweak.mk
