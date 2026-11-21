#!/usr/bin/env bash
# Axiom audit for the Lean development.
#
# Policy: this repository declares no axioms of its own. Every theorem may
# depend only on the axioms the base libraries already assume, namely
# propext, Classical.choice and Quot.sound (Lean/Mathlib; PhysLib adds none).
#
# The script
#   1. rejects any axiom/constant/opaque/unsafe/sorry/admit/native_decide,
#   2. collects every theorem name (tracking namespaces),
#   3. prints #print axioms for each and checks the reported sets.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PROJ="$ROOT/gravitation"
SRC="$PROJ/Gravitation"
GEN="$PROJ/.lake/audit_names.lean"
OUT="$PROJ/.lake/audit_axioms.txt"

echo "== 1. forbidden declarations =="
if grep -rnE "^[[:space:]]*(axiom|constant|opaque|unsafe)[[:space:]]|\bsorry\b|\badmit\b|native_decide|Lean\.trustCompiler" "$SRC"; then
  echo "FAIL: forbidden declaration or unfinished proof in $SRC"
  exit 1
fi
echo "none"

echo "== 2. collecting theorem names =="
NAMES=$(awk '
  /^namespace / { ns[++depth] = $2; next }
  /^end[[:space:]]/ { if (depth > 0) depth--; next }
  /^(theorem|lemma)[[:space:]]/ {
    # only real declarations: a bare identifier (possibly dotted) as the name
    if ($2 !~ /^[A-Za-z_][A-Za-z0-9_.]*$/) next
    full = ""
    for (i = 1; i <= depth; i++) full = full ns[i] "."
    print full $2
  }
' $(find "$SRC" -name '*.lean' | sort))

count=$(printf '%s\n' "$NAMES" | grep -c . || true)
echo "theorems found: $count"
if [ "$count" -lt 40 ]; then
  echo "FAIL: theorem extraction found too few names; check the awk rule"
  exit 1
fi

echo "== 3. checking axiom footprints =="
{
  echo "import Gravitation"
  printf '%s\n' "$NAMES" | sed 's/^/#print axioms /'
} > "$GEN"

cd "$PROJ"
export PATH="$HOME/.elan/bin:$PATH"
lake env lean "$GEN" > "$OUT" 2>&1 || true

reports=$(grep -c "depends on axioms\|does not depend on any axioms" "$OUT" || true)
echo "axiom reports: $reports / $count"
if [ "$reports" -ne "$count" ]; then
  echo "FAIL: some declarations produced no axiom report"
  grep '^#print axioms' "$GEN" | sed 's/#print axioms //' | sort > .lake/audit_names_sorted.txt
  grep -o "^'[^']*'" "$OUT" | tr -d "'" | sort > .lake/audit_reported.txt
  echo "names with no report:"
  comm -23 .lake/audit_names_sorted.txt .lake/audit_reported.txt | sed 's/^/  /'
  echo "compiler output (first lines):"
  sed -n '1,20p' "$OUT"
  exit 1
fi

bad=$(grep -o "\[[^]]*\]" "$OUT" \
  | tr -d '[]' \
  | tr ',' '\n' \
  | sed 's/^[[:space:]]*//; s/[[:space:]]*$//' \
  | grep -v '^$' \
  | sort -u \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)

if [ -n "$bad" ]; then
  echo "FAIL: axioms outside the base set:"
  printf '  %s\n' "$bad"
  exit 1
fi

if grep -q "sorryAx" "$OUT"; then
  echo "FAIL: sorryAx present"
  exit 1
fi

echo "PASS: $count theorems, axioms subset of {propext, Classical.choice, Quot.sound}"
