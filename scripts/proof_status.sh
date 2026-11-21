#!/usr/bin/env bash
# Maintains the proof-status table in README.md.
#
# Every declaration under gravitation/Gravitation/ is listed with the axioms its
# proof depends on, as reported by the audit.  A declaration is "proved" when the
# audit has a `#print axioms` report for it and that report stays inside the base
# axiom set; the audit itself fails first if any declaration uses `sorry` or
# declares an axiom of its own.
#
# Usage:
#   scripts/proof_status.sh           rewrite the table in README.md
#   scripts/proof_status.sh --check   fail if the table is out of date (CI)
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PROJ="$ROOT/gravitation"
DECLS="$PROJ/.lake/decls.tsv"
AXIOMS="$PROJ/.lake/axioms.tsv"
ROWS="$PROJ/.lake/proof_rows.tsv"
TABLE="$PROJ/.lake/proof_status.md"
README="$ROOT/README.md"
BEGIN='<!-- proof-status:begin -->'
END='<!-- proof-status:end -->'

mode="${1:-write}"

if [ ! -s "$DECLS" ] || [ ! -s "$AXIOMS" ]; then
  echo "== no declaration data yet, running the audit =="
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
    '$0 == b {on=1; next} $0 == e {on=0} on' "$README")"
  if [ "$current" = "$(cat "$TABLE")" ]; then
    echo "PASS: README proof-status table is current ($count declarations)."
    exit 0
  fi
  echo "FAIL: README proof-status table is out of date; run scripts/proof_status.sh"
  exit 1
fi

awk -v b="$BEGIN" -v e="$END" -v tbl="$TABLE" '
  $0 == b { print; while ((getline l < tbl) > 0) print l; skip = 1; next }
  $0 == e { print; skip = 0; next }
  !skip { print }
' "$README" > "$README.new" && mv "$README.new" "$README"
echo "wrote the proof-status table into README.md ($count declarations)"
