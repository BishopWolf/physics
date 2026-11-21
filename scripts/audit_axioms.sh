#!/usr/bin/env bash
# Axiom audit for the Lean development.
#
# Policy: this repository declares no axioms of its own. Every declaration may
# depend only on the axioms the base libraries already assume, namely
# propext, Classical.choice and Quot.sound (Lean/Mathlib; PhysLib adds none).
#
# The script
#   1. rejects any axiom/constant/opaque/unsafe/sorry/admit/native_decide,
#   2. collects every declaration (theorem, lemma, def, abbrev, structure,
#      inductive, class, instance) with its namespace,
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

echo "== 2. collecting declarations =="
DECLS=$(awk '
  BEGIN { incomment = 0 }
  /^[[:space:]]*\/-/ { incomment = 1; if ($0 ~ /-\//) incomment = 0; next }
  incomment { if ($0 ~ /-\//) incomment = 0; next }
  /^namespace / { ns[++depth] = $2; next }
  /^end[[:space:]]/ { if (depth > 0) depth--; next }
  /^@\[/ { next }
  $1 == "private" { next }
  {
    line = $0
    while (line ~ /^(noncomputable|protected|partial|nonrec|unsafe)[[:space:]]/) {
      sub(/^[A-Za-z_]+[[:space:]]+/, "", line)
    }
    if (line ~ /^(theorem|lemma|def|abbrev|structure|inductive|class|instance)[[:space:]]/) {
      rest = line
      sub(/^[A-Za-z_]+[[:space:]]+/, "", rest)
      name = rest
      sub(/[[:space:]].*/, "", name)
      if (name ~ /^[A-Za-z_][A-Za-z0-9_.]*$/) {
        full = ""
        for (i = 1; i <= depth; i++) full = full ns[i] "."
        print full name "\t" FILENAME "\t" FNR
      }
    }
  }
' $(find "$SRC" -name '*.lean' | sort))

printf '%s\n' "$DECLS" > "$PROJ/.lake/decls.tsv"
NAMES=$(printf '%s\n' "$DECLS" | cut -f1)

count=$(printf '%s\n' "$NAMES" | grep -c . || true)
theorems=$(grep -hE "^(theorem|lemma)[[:space:]]" $(find "$SRC" -name '*.lean') | wc -l)
echo "declarations found: $count (of which $theorems theorem-like)"
if [ "$count" -lt 100 ]; then
  echo "FAIL: declaration extraction found too few names; check the awk rule"
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

while IFS= read -r line; do
  case "$line" in
    \'*) ;;
    *) continue ;;
  esac
  nm=$(printf '%s' "$line" | cut -d"'" -f2)
  if printf '%s' "$line" | grep -q "does not depend on any axioms"; then
    printf '%s\t(none)\n' "$nm"
  else
    ax="${line#*\[}"
    ax="${ax%%\]*}"
    printf '%s\t%s\n' "$nm" "$ax"
  fi
done < "$OUT" > "$PROJ/.lake/axioms.tsv"

echo "PASS: $count declarations, axioms subset of {propext, Classical.choice, Quot.sound}"
