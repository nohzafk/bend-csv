#!/bin/sh
# csv-abnf's gate. Each step checks one claim, and each can fail:
#
#   1. the core checks, and no proof of it rests on unsafe code
#   2. the core builds into a typed module
#   3. a host reaches the parser through bridge.ts, including the refusals the
#      bridge owes a host (a separator the parser would read as itself)
#   4. it agrees with the reference on every small input, with the one known
#      difference class reported rather than hidden
#   5. every law is falsified on ~100k inputs, and the falsifier itself is
#      controlled -- a core with a planted bug must be refuted
#   6. every law is proved, by bend's checker
#   7. every law has a mutant: one planted edit to core.bend that makes it false
#      at a named input, and that law's own proof must fail where the table says
#   8. this library stands alone: nothing here imports from outside the repository
#
# Usage: sh test.sh

set -e
cd "$(dirname "$0")"

# The vendored code arrives as submodules, so a checkout without them is not
# broken, it is incomplete -- and this says which, instead of letting bend report
# a path it cannot find.
test -f vendor/bendlib/packages/bend-mathlib/string.bend || { echo "FAIL: vendor/bendlib is empty -- run: git submodule update --init"; exit 1; }
test -f vendor/bend-emit/src/emit.ts || { echo "FAIL: vendor/bend-emit is empty -- run: git submodule update --init"; exit 1; }

# The Bend release this repository declares (BEND_VERSION). When that release
# is not installed the gate skips itself, printing why.
WANT=$(cat BEND_VERSION)
HAVE=$(bend version 2>/dev/null | head -1)
case "$HAVE" in
  *"$WANT"*) ;;
  *) echo "SKIP: bend $WANT is not installed (found: ${HAVE:-nothing})"; exit 0 ;;
esac

echo "== 1. the core =="
OUT=$(bend --check-only core.bend 2>&1) || { echo "$OUT"; exit 1; }
echo "$OUT"
echo "$OUT" | grep -q "^ALL PROOFS CHECK" || { echo "FAIL: no ALL PROOFS CHECK verdict"; exit 1; }

echo "== 2. the module =="
# bend-emit exits 0 even when bend cannot compile the file, so the log is read
# rather than the exit code: otherwise the oracle below would measure a stale
# module.
rm -rf dist
bun ./vendor/bend-emit/src/emit.ts core.bend dist > /tmp/csv-abnf-emit.log 2>&1 || { cat /tmp/csv-abnf-emit.log; exit 1; }
grep -q "could not compile" /tmp/csv-abnf-emit.log && { cat /tmp/csv-abnf-emit.log; exit 1; }
test -s dist/core.mjs || { echo "FAIL: no module came out"; exit 1; }

echo "== 3. the bridge a host uses =="
bun check_bridge.ts || { echo "FAIL: the bridge does not do what it says"; exit 1; }

echo "== 4. the oracle =="
bun oracle.ts || { echo "FAIL: the parser and the reference part ways outside the known class"; exit 1; }

echo "== 5. the laws are falsified =="
if bun falsify.ts > /tmp/csv-abnf-falsify.log 2>&1; then
  tail -2 /tmp/csv-abnf-falsify.log
else
  grep -A2 REFUTED /tmp/csv-abnf-falsify.log
  echo "FAIL: a law is false as stated"
  exit 1
fi

# The control: the same sweep against a core with one planted bug. If the laws
# survive that, the falsifier is decoration.
rm -rf /tmp/csv-abnf-mutant && mkdir -p /tmp/csv-abnf-mutant
sed 's|sep, String.append(txt, one(c)), flds, rows)|sep, txt, flds, rows)|' core.bend > /tmp/csv-abnf-mutant/core.bend
grep -qF "sep, String.append(txt, one(c)), flds, rows)" core.bend || { echo "FAIL: the line the control plants a bug on is not in core.bend"; exit 1; }
test "$(grep -cF "sep, String.append(txt, one(c)), flds, rows)" /tmp/csv-abnf-mutant/core.bend)" = "0" || { echo "FAIL: the mutant was not planted"; exit 1; }
bun ./vendor/bend-emit/src/emit.ts /tmp/csv-abnf-mutant/core.bend /tmp/csv-abnf-mutant > /dev/null 2>&1
if CORE=/tmp/csv-abnf-mutant/core.mjs bun falsify.ts > /tmp/csv-abnf-control.log 2>&1; then
  tail -1 /tmp/csv-abnf-control.log
else
  cat /tmp/csv-abnf-control.log
  echo "FAIL: the falsifier caught nothing when the core was broken"
  exit 1
fi

echo "== 6. the proofs =="
OUT=$(bend --check-only PROOF.bend 2>&1) || { echo "$OUT"; echo "FAIL: the proofs do not check"; exit 1; }
echo "$OUT"
echo "$OUT" | grep -q "^ALL PROOFS CHECK" || { echo "FAIL: no ALL PROOFS CHECK verdict"; exit 1; }

echo "== 7. every law has a mutant that breaks its own proof =="
if ! bun check_mutants.ts > /tmp/csv-abnf-mutants.log 2>&1; then
  cat /tmp/csv-abnf-mutants.log
  echo "FAIL: a mutant check failed"
  exit 1
fi
tail -1 /tmp/csv-abnf-mutants.log

echo "== 8. this library stands alone =="
# Nothing reaches outside the checkout: a file below the root may import
# upwards within the project (native/bench.bend does), but nothing may climb
# past the root, and a root-level file may not climb at all.
if grep -rn --include='*.bend' --exclude-dir=vendor --exclude-dir=reference --exclude-dir=node_modules "\.\./\.\./" . ; then
  echo "FAIL: a file here imports from above the project"
  exit 1
fi
if grep -n --include='*.bend' "^import \.\./" *.bend ; then
  echo "FAIL: a file at the root imports from outside the project"
  exit 1
fi
echo "no file imports from outside the project"

echo "PASS: csv-abnf's gate"
