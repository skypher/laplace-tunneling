#!/usr/bin/env bash
# Build the Lean formalization and audit it.
# usage: ci/check.sh [-h|--help]
# Runs `lake build` (progress lines `[k/N] Built ...` are printed as modules
# finish), then fails if any declaration uses `sorry`, if any `axiom` is
# declared in the project sources, or if a final-facing theorem listed in
# ci/Axioms.lean depends on an axiom other than propext, Classical.choice,
# Quot.sound.
set -euo pipefail
if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  sed -n '2,8p' "$0" | sed 's/^# \{0,1\}//'
  exit 0
fi
cd "$(dirname "$0")/.."
echo "[ci] $(date -u +%FT%TZ) lake build"
stdbuf -oL lake build 2>&1 | tee ci-build.log
if grep -q "declaration uses .sorry." ci-build.log; then
  echo "[ci] FAIL: some declaration uses sorry"
  grep "declaration uses .sorry." ci-build.log
  exit 1
fi
if grep -rnE '^[[:space:]]*axiom[[:space:]]' Tunneling Tunneling.lean; then
  echo "[ci] FAIL: axiom declaration in project sources"
  exit 1
fi
echo "[ci] $(date -u +%FT%TZ) axiom audit"
stdbuf -oL lake env lean ci/Axioms.lean 2>&1 | tee ci-axioms.log
expected=$(grep -c '^#print axioms' ci/Axioms.lean)
clean=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ci-axioms.log || true)
if grep -q "sorryAx" ci-axioms.log || [[ "$clean" != "$expected" ]]; then
  echo "[ci] FAIL: axiom audit ($clean of $expected theorems clean)"
  exit 1
fi
echo "[ci] PASS: no sorry, no axiom declarations, $clean/$expected final theorems use only propext, Classical.choice, Quot.sound"
