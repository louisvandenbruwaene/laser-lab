#!/bin/bash
# Renders app/icon.icns from app/icon.html with headless Brave (no other renderer on this Mac).
set -euo pipefail
cd "$(dirname "$0")"
BRAVE="/Applications/Brave Browser.app/Contents/MacOS/Brave Browser"
tmp=$(mktemp -d); set=$tmp/icon.iconset; mkdir -p "$set"
"$BRAVE" --headless=new --disable-gpu --hide-scrollbars --default-background-color=00000000 \
  --window-size=1024,1024 --screenshot="$tmp/icon.png" "file://$PWD/icon.html" >/dev/null 2>&1
for s in 16 32 128 256 512; do
  sips -z $s $s "$tmp/icon.png" --out "$set/icon_${s}x${s}.png" >/dev/null
  sips -z $((s*2)) $((s*2)) "$tmp/icon.png" --out "$set/icon_${s}x${s}@2x.png" >/dev/null
done
iconutil -c icns "$set" -o icon.icns
cp "$tmp/icon.png" icon.png
rm -rf "$tmp"
echo "icon: $PWD/icon.icns"
