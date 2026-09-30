#!/bin/sh
# Fetch the reference parser (Deno's @std/csv, MIT) into reference/std.
#
# It is the oracle for oracle.ts and the baseline for the benchmarks. It is
# test code that this project only reads, so it is not committed: this script
# fetches the one pinned revision, and reference/ is in .gitignore.
#
# Usage: sh scripts/fetch-reference.sh
set -eu
cd "$(dirname "$0")/.."

PIN=cbfd1a98fdfc826fd2d35c1f8c31f7db7a063d26
URL=https://github.com/denoland/std
OUT=reference/std

if [ -f "$OUT/PIN" ] && [ "$(cat "$OUT/PIN")" = "$PIN" ] && [ -f "$OUT/parse.ts" ]; then
  echo "reference: already at ${PIN%"${PIN#???????}"}"
  exit 0
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
git init -q "$TMP"
git -C "$TMP" fetch -q --depth 1 "$URL" "$PIN"
git -C "$TMP" checkout -q FETCH_HEAD

rm -rf "$OUT"
mkdir -p "$OUT"
for f in parse.ts _io.ts _shared.ts; do
  cp "$TMP/csv/$f" "$OUT/$f"
done
cp "$TMP/LICENSE" "$OUT/LICENSE"
echo "$PIN" > "$OUT/PIN"
echo "reference: fetched @std/csv at $PIN into $OUT"
