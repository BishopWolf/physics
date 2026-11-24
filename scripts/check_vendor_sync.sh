#!/usr/bin/env bash
# Fail if the vendored copy of the Physlib `gravity` branch has drifted.
#
# `gravitation/vendor/` is a temporary, byte-for-byte copy of
# `PhyslibAlpha/Relativity/General/` at the commit recorded in
# `gravitation/vendor/REVISION`, except that import lines are rewritten from
# `PhyslibAlpha.Relativity.General.` to `Gravitation.Relativity.General.` so
# the modules do not collide with the dependency's own library globs.  This
# script fetches the branch and checks both that it still points at the
# recorded commit and that every vendored Lean file equals the branch file
# after applying the same rewrite.
#
# Requires network access and git; it runs in CI before the build.
set -euo pipefail
export LC_ALL=C

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VENDOR="$ROOT/gravitation/vendor"
REVFILE="$VENDOR/REVISION"
PREFIX="PhyslibAlpha/Relativity/General"
URL="https://github.com/BishopWolf/physlib.git"

if [ ! -f "$REVFILE" ]; then
  echo "FAIL: $REVFILE is missing"
  exit 1
fi
BRANCH="$(sed -n 's/^branch:[[:space:]]*//p' "$REVFILE" | tr -d '[:space:]')"
REV="$(sed -n 's/^commit:[[:space:]]*//p' "$REVFILE" | tr -d '[:space:]')"
BRANCH="${BRANCH:-gravity}"
if [ -z "$REV" ]; then
  echo "FAIL: no commit recorded in $REVFILE"
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git init -q "$TMP/repo"
git -C "$TMP/repo" remote add origin "$URL"

if ! git -C "$TMP/repo" fetch -q --depth 1 origin "$BRANCH" 2>/dev/null; then
  echo "FAIL: cannot fetch $URL branch $BRANCH"
  echo "      the branch may have been merged and deleted; re-vendor or migrate"
  exit 1
fi
TIP="$(git -C "$TMP/repo" rev-parse FETCH_HEAD)"
if [ "$TIP" != "$REV" ]; then
  echo "FAIL: $BRANCH tip is $TIP, vendored copy is at $REV"
  echo "      re-vendor the new commits (gravitation/vendor/README.md) or update"
  echo "      gravitation/vendor/REVISION if the difference is intentional"
  git -C "$TMP/repo" fetch -q --depth 1 origin "$REV" 2>/dev/null || true
  if git -C "$TMP/repo" cat-file -e "$REV^{commit}" 2>/dev/null; then
    git -C "$TMP/repo" diff --stat "$REV" FETCH_HEAD -- "$PREFIX" || true
  fi
  exit 1
fi

mismatch=0

# Every module on the branch (except the already-merged IncompressibleSphere)
# must be present in the vendored tree, identical up to the import rewrite.
while IFS= read -r path; do
  rel="${path#"$PREFIX"/}"
  [ "$rel" = "Schwarzschild/IncompressibleSphere.lean" ] && continue
  expected="$TMP/expected/$rel"
  mkdir -p "$(dirname "$expected")"
  git -C "$TMP/repo" show "FETCH_HEAD:$path" \
    | sed 's/PhyslibAlpha\.Relativity\.General\./Gravitation.Relativity.General./g' \
    > "$expected"
  actual="$VENDOR/Gravitation/Relativity/General/$rel"
  if [ ! -f "$actual" ]; then
    echo "missing from vendor: $rel"
    mismatch=1
    continue
  fi
  if ! diff -q "$expected" "$actual" >/dev/null; then
    echo "drifted from $BRANCH: $rel"
    diff -u "$expected" "$actual" | head -20 || true
    mismatch=1
  fi
done < <(git -C "$TMP/repo" ls-tree -r --name-only FETCH_HEAD "$PREFIX" \
         | grep '\.lean$' || true)

# No extra vendored Lean files.
while IFS= read -r actual; do
  rel="${actual#"$VENDOR/Gravitation/Relativity/General/"}"
  if ! git -C "$TMP/repo" cat-file -e "FETCH_HEAD:$PREFIX/$rel" 2>/dev/null; then
    echo "not on $BRANCH: $rel"
    mismatch=1
  fi
done < <(find "$VENDOR/Gravitation/Relativity/General" -name '*.lean')

if [ "$mismatch" -ne 0 ]; then
  echo "FAIL: the vendored copy differs from $URL $BRANCH @ $REV"
  echo "      re-copy PhyslibAlpha/Relativity/General, rewrite the imports and"
  echo "      update gravitation/vendor/REVISION (see gravitation/vendor/README.md)"
  exit 1
fi

echo "PASS: vendored copy matches $URL $BRANCH @ $REV"
