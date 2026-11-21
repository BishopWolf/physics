#!/usr/bin/env bash
# Maintains the proof-status table in Proof-Status.md.
#
# Every declaration under gravitation/Gravitation/ is listed with the axioms its
# proof depends on, as reported by the audit.  A declaration is "proved" when the
# audit has a `#print axioms` report for it and that report stays inside the base
# axiom set; the audit itself fails first if any declaration uses `sorry` or
# declares an axiom of its own.
#
# Usage:
#   scripts/proof_status.sh           rewrite the table in Proof-Status.md
#   scripts/proof_status.sh --check   fail if the table is out of date (CI)
set -uo pipefail

# `sort` collation depends on the locale, and the proof-status table is sorted:
# CI's C locale ordered the rows differently from a developer machine's fr_FR,
# so the same commit produced a table only one of the two accepted.  Pin the
# locale so every run builds a byte-identical table.
export LC_ALL=C

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PROJ="$ROOT/gravitation"
DECLS="$PROJ/.lake/decls.tsv"
AXIOMS="$PROJ/.lake/axioms.tsv"
ROWS="$PROJ/.lake/proof_rows.tsv"
TABLE="$PROJ/.lake/proof_status.md"
PAGE="$ROOT/Proof-Status.md"
BEGIN='<!-- proof-status:begin -->'
END='<!-- proof-status:end -->'

mode="${1:-write}"

# Never trust audit data left over from an earlier build.  The CI cache restores
# gravitation/.lake (keyed on the toolchain and manifest, not on the commit), and
# a local tree can hold TSVs from before the last edit; either way the table
# would look current while the sources have moved on.  Refresh the data when it
# is missing or older than the newest source file, so a `--check` in CI and a
# `--check` on a developer machine compare the page against the same extraction.
stale=0
if [ ! -s "$DECLS" ] || [ ! -s "$AXIOMS" ]; then
  stale=1
elif [ -n "$(find "$PROJ/Gravitation" -name '*.lean' -newer "$DECLS" -print -quit)" ]; then
  stale=1
fi

if [ "$stale" = 1 ]; then
  echo "== refreshing declaration and axiom data =="
  bash "$ROOT/scripts/audit_axioms.sh" >/dev/null || {
    echo "FAIL: audit failed, cannot build the proof-status table"
    exit 1
  }
fi

# decls.tsv: name <TAB> file <TAB> line   (~ sorted by file, line)
# axioms.tsv: name <TAB> axiom list
awk -F'\t' '
  FNR == NR { ax[$1] = $2; next }
  { st = ($1 in ax) ? "proved" : "unverified"
    print $2 "\t" $3 "\t" $1 "\t" (($1 in ax) ? ax[$1] : "-") "\t" st }
' "$AXIOMS" "$DECLS" | sort -t$'\t' -k1,1 -k2,2n > "$ROWS"

{
  echo "| Declaration | File | Axioms | Status |"
  echo "| --- | --- | --- | --- |"
  awk -F'\t' '{
    f = $1; sub(/.*\//, "", f)
    printf "| `%s` | `%s` | %s | %s |\n", $3, f, $4, $5
  }' "$ROWS"
} > "$TABLE"

count=$(($(wc -l < "$TABLE") - 2))

if [ "$mode" = "--check" ]; then
  current="$(awk -v b="$BEGIN" -v e="$END" \
    '$0 == b {on=1; next} $0 == e {on=0} on' "$PAGE")"
  if [ "$current" = "$(cat "$TABLE")" ]; then
    echo "PASS: Proof-Status.md table is current ($count declarations)."
    exit 0
  fi
  echo "FAIL: Proof-Status.md table is out of date; run scripts/proof_status.sh"
  exit 1
fi

awk -v b="$BEGIN" -v e="$END" -v tbl="$TABLE" '
  $0 == b { print; while ((getline l < tbl) > 0) print l; skip = 1; next }
  $0 == e { print; skip = 0; next }
  !skip { print }
' "$PAGE" > "$PAGE.new" && mv "$PAGE.new" "$PAGE"
echo "wrote the proof-status table into Proof-Status.md ($count declarations)"
