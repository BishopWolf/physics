#!/usr/bin/env bash
# Checks that the declaration census in docs/Gravitation-Formalisation.md
# matches the axiom audit's per-module counts.
#
# Usage: scripts/check_census.sh
set -uo pipefail

export LC_ALL=C

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PROJ="$ROOT/gravitation"
DECLS="$PROJ/.lake/decls.tsv"
PAGE="$ROOT/docs/Gravitation-Formalisation.md"

if [ ! -s "$DECLS" ]; then
  echo "== extracting declaration data =="
  bash "$ROOT/scripts/audit_axioms.sh" >/dev/null || {
    echo "FAIL: audit failed, cannot check the census"
    exit 1
  }
fi

ROWS="$(mktemp)"
ACTUAL="$(mktemp)"
trap 'rm -f "$ROWS" "$ACTUAL"' EXIT

# Appendix A rows: | `Module` | count |
awk -F'|' '
  /^\| `[^`]+` \| [0-9]+ \|$/ {
    name = $2; gsub(/^[[:space:]]*`|`[[:space:]]*$/, "", name)
    count = $3; gsub(/[[:space:]]/, "", count)
    print name "\t" count
  }
' "$PAGE" | sort > "$ROWS"

# The audit TSV stores the source path; a module name is that path without
# `.lean` and with `/` replaced by `.`.
awk -F'\t' '
  {
    path = $2
    sub(/\.lean$/, "", path)
    gsub(/\//, ".", path)
    count[path]++
  }
  END { for (m in count) print m "\t" count[m] }
' "$DECLS" | sort > "$ACTUAL"

if ! diff -u "$ACTUAL" "$ROWS"; then
  echo "FAIL: census table does not match the per-module audit counts"
  echo "      (left: audit, right: docs/Gravitation-Formalisation.md)"
  exit 1
fi

rows_total=$(awk -F'\t' '{ s += $2 } END { print s + 0 }' "$ROWS")
decls_total=$(wc -l < "$DECLS")
table_total=$(awk -F'|' '
  /^\| \*\*Total\*\* \| \*\*[0-9]+\*\* \|$/ {
    t = $3; gsub(/[^0-9]/, "", t); print t
  }
' "$PAGE")

if [ "$rows_total" != "$decls_total" ] || [ "$table_total" != "$decls_total" ]; then
  echo "FAIL: census totals disagree with the audit"
  echo "      audit declarations: $decls_total"
  echo "      table row sum:     $rows_total"
  echo "      table Total row:   ${table_total:-missing}"
  exit 1
fi

echo "PASS: census matches the audit ($decls_total declarations)."
