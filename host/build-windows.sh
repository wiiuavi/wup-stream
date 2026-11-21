#!/bin/sh
# Cross-build the self-contained x64 Windows streamer from Linux with MinGW-w64.
set -eu
cd "$(dirname "$0")/.."
B=build/host; X=$B/x264-win-asm; CC=x86_64-w64-mingw32-gcc-posix; CXX=x86_64-w64-mingw32-g++-posix
command -v "$CC" >/dev/null || { echo "Install mingw-w64 (x86_64-w64-mingw32) first" >&2; exit 1; }
mkdir -p "$B" "$X"
if [ ! -f "$X/libx264.a" ]; then
  if [ ! -d "$X/.git" ]; then
    git init -q "$X"
    git -C "$X" fetch -q --depth 1 https://code.videolan.org/videolan/x264.git b35605ace3ddf7c1a5d67a2eb553f034aef41d55
    git -C "$X" checkout -q FETCH_HEAD
    git -C "$X" apply "$PWD/host/x264-drh-mode.patch"
  fi
  ASM=; command -v nasm >/dev/null || ASM=--disable-asm
  (cd "$X" && ./configure --host=x86_64-w64-mingw32 --cross-prefix=x86_64-w64-mingw32- --enable-static --disable-cli --disable-opencl --bit-depth=8 $ASM >/dev/null && make -j8 libx264.a >/dev/null 2>&1)
fi
"$CC" -O2 -Wall -I"$X" -c host/wupstream.c -o "$B/wupstream-win.o"
cp "$X/libx264.a" "$B/libwupstream-win.a"
x86_64-w64-mingw32-ar rs "$B/libwupstream-win.a" "$B/wupstream-win.o" >/dev/null
mkdir -p dist
"$CXX" -O2 -Wall -static -static-libgcc -static-libstdc++ -Ihost -I"$X" host/windows_streamer.cpp "$B/libwupstream-win.a" \
  -lws2_32 -lwinmm -lgdi32 -lole32 -luuid -lavrt -lcomctl32 -lshell32 -o dist/wup-stream.exe
echo "Built dist/wup-stream.exe"
