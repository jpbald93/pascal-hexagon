#!/bin/bash
# Tampering tests for gate.sh. Each test copies the repository to a scratch directory,
# plants one defect, runs the gate there, and expects it to FAIL at the stated stage.
# The real repository is never modified. Tests run one at a time (Lean builds are memory-heavy).
# The scratch copies reuse the prebuilt project oleans in .lake/build (lake re-checks them by
# hash), so only the planted file and its dependents are re-elaborated. Defects are planted in
# PascalHexagon/Correctness.lean, the last module, so the 90 s `ring` modules are not rebuilt.
# Usage: bash tests/tamper.sh            (all tests)
#        bash tests/tamper.sh sorry wrap (a subset)
# Exit status 0 iff every selected test is rejected with the expected message.
set -u
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/pascal_tamper_XXXX")"
C=PascalHexagon/Correctness.lean
E='^end PascalHexagon'
[ -e "$SRC/.lake/packages/mathlib" ] || (cd "$SRC" && lake exe cache get) || { echo "cannot fetch Mathlib"; exit 1; }
PK="$(cd "$SRC/.lake/packages" && pwd -P)"

mk() {  # fresh copy sharing the prebuilt Mathlib packages
  mkdir -p "$WORK/$1/.lake"
  cp -r "$SRC"/{PascalHexagon,PascalHexagon.lean,gate.sh,lake-manifest.json,lakefile.toml,lean-toolchain} "$WORK/$1/"
  ln -s "$PK" "$WORK/$1/.lake/packages"
  [ -d "$SRC/.lake/build" ] && cp -a "$SRC/.lake/build" "$WORK/$1/.lake/build"
}

plant() {
  local d="$WORK/$1"
  case "$1" in
    sorry)    sed -i "s|$E|theorem bogus : (1:ℕ) = 2 := by sorry\nend PascalHexagon|" "$d/$C" ;;
    ax2line)  sed -i "s|$E|axiom\n  cheat_unused : False\nend PascalHexagon|" "$d/$C" ;;
    evalfake) sed -i "s|$E|#eval IO.println \"'PascalHexagon.pascal' depends on axioms: [propext]\"\nend PascalHexagon|" "$d/$C" ;;
    macro)    python3 - "$d/$C" <<'PY'
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text()
m = ("macro_rules\n  | `(#print axioms $id:ident) =>\n"
     "    `(#print $(Lean.Syntax.mkStrLit s!\"'{id.getId}' depends on axioms: [propext]\"))\n")
p.write_text(s.replace("end PascalHexagon", m + "end PascalHexagon"))
PY
              ;;
    falsehyp) # Pappus with E moved from line a to line b: no longer a line-pair configuration.
              sed -i 's|(hA : A.orthogonal a) (hC : C.orthogonal a) (hE : E.orthogonal a)|(hA : A.orthogonal a) (hC : C.orthogonal a) (hE : E.orthogonal b)|' "$d/$C"
              grep -q '(hE : E.orthogonal b)' "$d/$C" || return 1 ;;
    wrap)     # Tests the output parser alone: the source filter's `axiom` check is switched off in
              # this copy's gate, and a long-named extra axiom is smuggled into a main theorem so
              # that Lean wraps it onto a continuation line of the #print axioms report.
              python3 - "$d/$C" <<'PY'
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text()
s = s.replace("theorem pappus {", "theorem pappus_orig {", 1)
s = s.replace("end PascalHexagon",
  "axiom zz_extra_axiom_with_a_long_name_for_the_negative_gate_test : True\n"
  "theorem pappus : True := by\n"
  "  have := @pappus_orig.{0}\n  exact zz_extra_axiom_with_a_long_name_for_the_negative_gate_test\n\n"
  "end PascalHexagon", 1)
p.write_text(s)
PY
              grep -q 'theorem pappus_orig' "$d/$C" || return 1
              sed -i 's/|\\baxiom\\b//' "$d/gate.sh"
              ! grep -q 'baxiom' "$d/gate.sh" || return 1 ;;
    *) return 1 ;;
  esac
}

expect() { case "$1" in
  sorry|ax2line|evalfake|macro) echo "FAIL: forbidden token" ;;
  falsehyp) echo "FAIL: build" ;;
  wrap) echo "FAIL: nonstandard axioms" ;;
esac; }

TESTS="${*:-sorry ax2line evalfake macro falsehyp wrap}"
bad=0
for t in $TESTS; do
  mk "$t"
  if ! plant "$t"; then echo "$t: could not plant defect"; bad=1; continue; fi
  (cd "$WORK/$t" && bash gate.sh > gate.log 2>&1)
  got="$(grep -E '^(PASS|FAIL)' "$WORK/$t/gate.log" | tail -1)"
  want="$(expect "$t")"
  if [[ "$got" == "$want"* ]]; then printf 'ok    %-9s rejected: %s\n' "$t" "$got"
  else printf 'NOT OK %-9s expected "%s", got "%s" (log: %s)\n' "$t" "$want" "$got" "$WORK/$t/gate.log"; bad=1; fi
  rm -rf "$WORK/$t/.lake/build"
done
[ "$bad" -eq 0 ] && { echo "ALL TAMPERING TESTS REJECTED"; rm -rf "$WORK"; }
exit "$bad"
