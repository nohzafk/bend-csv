#!/bin/sh
# Build the delivery module: core.bend -> dist/core.mjs + dist/core.d.mts.
# The one build used by contributors, test.sh and CI.
#
#   sh scripts/build.sh [source.bend] [outdir]     (default: core.bend dist)
#
# Needs bend (exactly the version in BEND_VERSION), bun and npx on PATH.
# Users of the library do not run this: dist/ is committed.
#
# The emitter is a fixed published npm version installed as a devDependency.
# npx is used only as a local runner; --no-install prevents implicit downloads.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
SRC=${1:-$ROOT/core.bend}
OUT=${2:-$ROOT/dist}
die() { echo "build: FAIL: $*" >&2; exit 1; }

WANT=$(tr -d ' \r\n' < "$ROOT/BEND_VERSION")
HAVE=$(bend version 2>/dev/null | head -1) || true
test "$HAVE" = "bend $WANT" || die "needs exactly bend $WANT (found: ${HAVE:-nothing})"
command -v bun >/dev/null || die "bun not on PATH (the emitter runs under bun)"
command -v npx >/dev/null || die "npx not on PATH"
test -f "$SRC" || die "no such source: $SRC"

NAME=$(basename "$SRC" .bend)
# Remove old outputs first, so a failed build never leaves a stale module.
rm -f "$OUT/$NAME.mjs" "$OUT/$NAME.d.mts"
TMP=$(mktemp -d "${TMPDIR:-/tmp}/bend-csv-build.XXXXXX")
trap 'rm -rf "$TMP"' EXIT

# The emitter can exit 0 although bend could not compile: read its log too.
if ! npx --no-install bend-emit "$SRC" "$TMP" > "$TMP/emit.log" 2>&1; then
  cat "$TMP/emit.log" >&2; die "bend-emit failed on $SRC"
fi
if grep -q "could not compile" "$TMP/emit.log"; then
  cat "$TMP/emit.log" >&2; die "bend could not compile $SRC"
fi
test -s "$TMP/$NAME.mjs" || die "no $NAME.mjs produced"
test -s "$TMP/$NAME.d.mts" || die "no $NAME.d.mts produced"
grep -q "^export " "$TMP/$NAME.d.mts" || die "$NAME.d.mts declares nothing"
grep -q "^export " "$TMP/$NAME.mjs" || die "$NAME.mjs exports nothing"
# Deterministic: no temp path may leak into the artifacts.
if grep -qF "$TMP" "$TMP/$NAME.mjs" "$TMP/$NAME.d.mts"; then die "temp path leaked into output"; fi

mkdir -p "$OUT"
cp "$TMP/$NAME.mjs" "$TMP/$NAME.d.mts" "$OUT/"
# Read the emitter's own version rather than repeating it here, so a bump
# cannot leave this line naming an emitter that is not the one installed.
EMITTER=$(sed -n 's/.*"version": *"\([^"]*\)".*/\1/p' "$ROOT/node_modules/bend-emit/package.json" 2>/dev/null | head -1)
echo "build: wrote $OUT/$NAME.mjs and $OUT/$NAME.d.mts (bend $WANT, bend-emit ${EMITTER:-unknown})"
