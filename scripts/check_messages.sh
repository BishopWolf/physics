#!/usr/bin/env bash
# Fail unless `lake build` is silent.
#
# The rule for this repository is that the build emits no Lean messages at all.
# Lake's module-system advisory (once per Mathlib import) is opted out in
# lakefile.toml via `allowNonModules`; the filter below is only a safety net so
# a future toolchain change cannot turn it into a spurious failure.
set -uo pipefail
cd "$(dirname "$0")/../gravitation"
export PATH="${HOME}/.elan/bin:${PATH}"

log=".lake/build_messages.log"
lake build >"${log}" 2>&1
status=$?
if [ "${status}" -ne 0 ]; then
  echo "FAIL: lake build exited ${status}"
  tail -40 "${log}"
  exit 1
fi

messages="$(grep -E '^(error|warning):' "${log}" \
  | grep -v 'designed for use with the module system' \
  | grep -v '^warning: vendor/' \
  | grep -v '^\(warning\|error\): .*vendor/' || true)"
if [ -n "${messages}" ]; then
  echo "FAIL: the build emitted Lean messages:"
  echo "${messages}"
  exit 1
fi
echo "PASS: build emitted no Lean messages."
