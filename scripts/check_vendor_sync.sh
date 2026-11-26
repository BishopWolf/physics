#!/usr/bin/env bash
# Fail if the vendored copy of the Physlib `gravity` branch has drifted.
#
# `gravitation/vendor/` is a temporary, byte-for-byte copy of four subtrees at
# the commit recorded in `gravitation/vendor/REVISION`:
#
#   PhyslibAlpha/Relativity/General/   -> Gravitation/Relativity/General/
#   PhyslibAlpha/Relativity/Metrics/   -> Gravitation/Relativity/Metrics/
#   PhyslibAlpha/Relativity/Tensors/   -> Gravitation/Relativity/Tensors/
#   PhyslibAlpha/Cosmology/            -> Gravitation/Cosmology/
#
# Import lines are rewritten from `PhyslibAlpha.*` to `Gravitation.*` so the
# modules do not collide with the dependency's own library globs.  No local
# compatibility patch is applied: the branch itself dropped
# `ReferenceFrame.IsMetricConserved` in `296991d`.  This script fetches the
# branch and checks both that it still points at the recorded commit and that
# every vendored Lean file equals the branch file after applying the same
# rewrites.
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

declare -A EXPECTED
mismatch=0

rewrite() {
  sed \
    -e 's/PhyslibAlpha\.Relativity\.General\./Gravitation.Relativity.General./g' \
    -e 's/PhyslibAlpha\.Relativity\.Metrics\./Gravitation.Relativity.Metrics./g' \
    -e 's/PhyslibAlpha\.Relativity\.Tensors\./Gravitation.Relativity.Tensors./g' \
    -e 's/PhyslibAlpha\.Cosmology\./Gravitation.Cosmology./g' \
    -e 's/Gravitation\.Relativity\.General\.Schwarzschild\.IncompressibleSphere/PhyslibAlpha.Relativity.General.Schwarzschild.IncompressibleSphere/g'
}

check_subtree() {
  local src="$1" dest="$2" mode="$3" list="$4"
  local rel expected actual
  local -a rels=()

  if [ "$mode" = all ]; then
    mapfile -t rels < <(git -C "$TMP/repo" ls-tree -r --name-only FETCH_HEAD "$src" \
      | sed "s#^$src/##" | grep '\.lean$' | sort)
  else
    mapfile -t rels < <(printf '%s\n' "$list" | tr ',' '\n' | sed '/^$/d')
  fi

  for rel in "${rels[@]}"; do
    if [ "$src" = "PhyslibAlpha/Relativity/General" ] && \
       [ "$rel" = "Schwarzschild/IncompressibleSphere.lean" ]; then
      continue
    fi
    EXPECTED["$dest/$rel"]=1
    expected="$TMP/expected/$dest/$rel"
    mkdir -p "$(dirname "$expected")"
    git -C "$TMP/repo" show "FETCH_HEAD:$src/$rel" | rewrite > "$expected"
    actual="$VENDOR/$dest/$rel"
    if [ ! -f "$actual" ]; then
      echo "missing from vendor: $dest/$rel"
      mismatch=1
      continue
    fi
    if ! diff -q "$expected" "$actual" >/dev/null; then
      echo "drifted from $BRANCH: $dest/$rel"
      diff -u "$expected" "$actual" | head -20 || true
      mismatch=1
    fi
  done

  while IFS= read -r actual; do
    rel="${actual#"$VENDOR/$dest/"}"
    if [ -z "${EXPECTED["$dest/$rel"]+x}" ]; then
      echo "not on $BRANCH: $dest/$rel"
      mismatch=1
    fi
  done < <(find "$VENDOR/$dest" -name '*.lean' 2>/dev/null || true)
}

check_subtree "PhyslibAlpha/Relativity/General" "Gravitation/Relativity/General" all ""
check_subtree "PhyslibAlpha/Relativity/Metrics" "Gravitation/Relativity/Metrics" all ""
check_subtree "PhyslibAlpha/Relativity/Tensors" "Gravitation/Relativity/Tensors" allow \
  "Tensor2.lean,RiemannTensor.lean,RicciTensor.lean,EinsteinTensor.lean,MaxwellStressEnergy.lean,EMFieldStrength.lean"
check_subtree "PhyslibAlpha/Cosmology" "Gravitation/Cosmology" all ""

if [ "$mismatch" -ne 0 ]; then
  echo "FAIL: the vendored copy differs from $URL $BRANCH @ $REV"
  echo "      re-copy the four subtrees, rewrite the imports, re-apply the MOND"
  echo "      patch and update gravitation/vendor/REVISION (see vendor/README.md)"
  exit 1
fi

echo "PASS: vendored copy matches $URL $BRANCH @ $REV"
