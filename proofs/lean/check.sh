#!/usr/bin/env bash
# Check the Lean proofs of kovan (the library in this directory).
#   bash proofs/lean/check.sh          the scan for unfinished proofs, the build, then the axioms
#   bash proofs/lean/check.sh build    `lake build`, failing on any warning
#   bash proofs/lean/check.sh sorry    fail if `sorry` or `admit` appears in a Lean source
#   bash proofs/lean/check.sh axioms   fail unless every theorem rests only on Lean's own axioms
# Lean accepts a proof with a hole in it (`sorry`, `admit`) and only warns, so the build fails on
# any warning and the scan fails on either word anywhere in a Lean source, comments included:
# a proof with a hole is not a proof. The axiom check compiles Axioms.lean, which walks every
# theorem of the library and fails naming any that rests on an axiom other than propext,
# Quot.sound and Classical.choice (a hole shows there as sorryAx). The build needs `lake` on PATH
# (elan installs it, and fetches the Lean release lean-toolchain names on first use; see README.md).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"

scan() {
  local status=0
  grep -rnwE --include='*.lean' --exclude-dir=.lake 'sorry|admit' "$here" || status=$?
  case "$status" in
    0) echo "the Lean proofs above are unfinished: remove every sorry and admit" >&2; return 1 ;;
    1) echo "no sorry and no admit in the Lean sources" ;;
    *) echo "could not scan the Lean sources" >&2; return 1 ;;
  esac
}

build() {
  command -v lake >/dev/null || {
    echo "lake is not on PATH: install elan, see proofs/lean/README.md" >&2; return 1; }
  (cd "$here" && lake build --wfail)
}

axioms() {
  build && (cd "$here" && lake env lean Axioms.lean)
}

case "${1:-all}" in
  sorry) scan ;;
  build) build ;;
  axioms) axioms ;;
  all) scan && axioms ;;
  *) echo "usage: check.sh [all|build|sorry|axioms]" >&2; exit 2 ;;
esac
