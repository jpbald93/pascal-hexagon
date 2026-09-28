import PascalHexagon.Defs
import Mathlib.Tactic.Ring

open Matrix

namespace PascalHexagon

variable {K : Type*} [CommRing K]

/-- The 6×6 Veronese determinant is minus the Pascal bracket polynomial
(any commutative ring, no hypotheses). -/
theorem det_verMatrix_eq_neg_pascalBracket (A B C D E F : Fin 3 → K) :
    (verMatrix A B C D E F).det = -pascalBracket A B C D E F := by
  simp [verMatrix, pascalBracket, det_succ_row_zero, Fin.sum_univ_succ, ver, Fin.succAbove]
  simp only [br, cross_apply, vec3_dotProduct, cons_val_zero, cons_val_one, cons_val_two,
    Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons]
  ring

end PascalHexagon
