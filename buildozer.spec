[app]

# ---- المعلومات الأساسية
title = Elint Map Downloader
package.name = mapdownloader
package.domain = org.elint

# ---- الملفات (الملف الرئيسي يجب أن يكون main.py بعد إعادة تسمية Map_Downloader.py)
source.dir = .
source.include_exts = py,png,jpg,ttf
source.exclude_dirs = bin, .buildozer, venv, __pycache__, .git, .github, Output
source.exclude_patterns = *.pem, *.csv, *.log

version = 1.1.0

# ---- المكتبات المطلوبة لتطبيق الخرائط
requirements = python3,kivy==2.3.0,pillow,certifi,pyjnius,android

# ---- الواجهة
orientation = portrait
fullscreen = 0

icon.filename = %(source.dir)s/icon.png
presplash.filename = %(source.dir)s/splash.png
presplash.color = #0C0E13

# ---- أندرويد (نفس الإعدادات الناجحة)
android.api = 33
android.minapi = 24
android.ndk = 25b
android.ndk_api = 24
android.archs = arm64-v8a, armeabi-v7a
android.accept_sdk_license = True
android.allow_backup = False

# صلاحيات التخزين الكاملة لحفظ البلاطات
android.permissions = READ_EXTERNAL_STORAGE,WRITE_EXTERNAL_STORAGE,MANAGE_EXTERNAL_STORAGE

# ---- python-for-android
p4a.branch = v2024.01.21

[buildozer]
log_level = 2
warn_on_root = 1
