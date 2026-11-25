#!/usr/bin/env bash
# Axiom audit for the Lean development and its Physlib dependency.
#
# Policy: neither this repository nor the general-relativity development it
# consumes declares axioms of its own. Every declaration may depend only on the
# axioms the base libraries already assume, namely propext, Classical.choice
# and Quot.sound (Lean/Mathlib; Physlib adds none).
#
# The development audited here is the repository's own module (the umbrella
# `Gravitation` root) together with the full vendored `gravity` tree and the
# `PhyslibAlpha/Relativity/General/` modules left in the pinned Physlib revision
# (`Schwarzschild/IncompressibleSphere`): the theorems this repository reports on
# are the Physlib ones, so the audit has to cover them, not just the local imports.
#
# The script
#   1. rejects any axiom/constant/opaque/unsafe/sorry/admit/native_decide,
#   2. collects every declaration (theorem, lemma, def, abbrev, structure,
#      inductive, class, instance) with its namespace,
#   3. prints #print axioms for each and checks the reported sets.
set -euo pipefail

# `sort` collation depends on the locale, and the proof-status table is sorted:
# CI's C locale ordered the rows differently from a developer machine's fr_FR,
# so the same commit produced a table only one of the two accepted.  Pin the
# locale so every run builds a byte-identical table.
export LC_ALL=C

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PROJ="$ROOT/gravitation"
SRC="$PROJ/Gravitation"
PKG="$PROJ/.lake/packages/physlib"
DEP="$PKG/PhyslibAlpha/Relativity/General"
VENDOR="$PROJ/vendor/Gravitation"
GEN="$PROJ/.lake/audit_names.lean"
OUT="$PROJ/.lake/audit_axioms.txt"

if [ ! -d "$VENDOR" ] || [ ! -d "$DEP" ]; then
  echo "FAIL: audited sources not found under $VENDOR or $DEP"
  echo "      run 'cd gravitation && lake build' first"
  exit 1
fi

FILES=$(find "$SRC" "$VENDOR" "$DEP" -name '*.lean' | sort)

echo "== 1. forbidden declarations =="
# Scan code only: module docstrings in Physlib start at column 0 and contain
# words such as "constant", so a plain grep would report prose as a declaration.
# This strips `/- ... -/` blocks and `--` comments before looking for axioms,
# `sorry`, `admit`, `native_decide` or `Lean.trustCompiler`.
forbidden=$(awk '
  BEGIN { incomment = 0 }
  {
    line = $0
    out = ""
    i = 1
    n = length(line)
    while (i <= n) {
      if (incomment) {
        p = index(substr(line, i), "-/")
        if (p == 0) { i = n + 1; break }
        i = i + p + 1
        incomment = 0
        out = out " "
      } else {
        rest = substr(line, i)
        p1 = index(rest, "/-")
        p2 = index(rest, "--")
        if (p1 == 0 && p2 == 0) { out = out rest; break }
        if (p1 != 0 && (p2 == 0 || p1 < p2)) {
          out = out substr(rest, 1, p1 - 1)
          after = substr(rest, p1 + 2)
          q = index(after, "-/")
          if (q == 0) { incomment = 1; break }
          i = i + p1 + 1 + q + 1
        } else {
          out = out substr(rest, 1, p2 - 1)
          break
        }
      }
    }
    if (out ~ /(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)/ ||
        out ~ /(^|[^A-Za-z0-9_])admit([^A-Za-z0-9_]|$)/ ||
        out ~ /native_decide/ || out ~ /Lean\.trustCompiler/) {
      print FILENAME ":" FNR ": " $0
    } else if (out ~ /^[[:space:]]*(axiom|constant|opaque|unsafe)[[:space:]]/) {
      print FILENAME ":" FNR ": " $0
    }
  }
' $FILES)
if [ -n "$forbidden" ]; then
  printf '%s\n' "$forbidden"
  echo "FAIL: forbidden declaration or unfinished proof in the audited sources"
  exit 1
fi
echo "none"

echo "== 2. collecting declarations =="
DECLS=$(awk -v proj="$PROJ/" -v pkg="$PKG/" '
  BEGIN { incomment = 0 }
  /^[[:space:]]*\/-/ { incomment = 1; if ($0 ~ /-\//) incomment = 0; next }
  incomment { if ($0 ~ /-\//) incomment = 0; next }
  /^namespace / { ns[++depth] = $2; next }
  /^end([[:space:]]|$)/ {
    if (depth > 0 && (NF == 1 || $2 == ns[depth])) depth--
    next
  }
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
        fname = FILENAME
        sub("^" pkg, "", fname)
        sub("^" proj, "", fname)
        sub("^vendor/", "", fname)
        print full name "\t" fname "\t" FNR
      }
    }
  }
' $FILES)

printf '%s\n' "$DECLS" > "$PROJ/.lake/decls.tsv"
NAMES=$(printf '%s\n' "$DECLS" | cut -f1)

count=$(printf '%s\n' "$NAMES" | grep -c . || true)
theorems=$(grep -hE "^(theorem|lemma)[[:space:]]" $FILES | wc -l)
echo "declarations found: $count (of which $theorems theorem-like)"
if [ "$count" -lt 400 ]; then
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
lake env lean "$GEN" > "$OUT.raw" 2>&1 || true
awk '/^[[:space:]]/ && have_prev { prev = prev $0; next } have_prev { print prev } { prev = $0; have_prev = 1 } END { if (have_prev) print prev }' "$OUT.raw" > "$OUT"

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
