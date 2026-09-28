import PascalHexagon.Defs
import Mathlib.Tactic.Ring

/-!
# Stage 1: Pascal on the standard conic `xz = y²`

Direct `ring` proof for points `(sᵢ², sᵢtᵢ, tᵢ²)` (every point of `xz = y²` over an
algebraically closed field has this form). Independent of the Veronese identity.
-/

open Matrix

namespace PascalHexagon

variable {K : Type*} [CommRing K]

theorem pascalDet_standardConic (s t : Fin 6 → K) :
    pascalDet ![s 0 ^ 2, s 0 * t 0, t 0 ^ 2] ![s 1 ^ 2, s 1 * t 1, t 1 ^ 2]
      ![s 2 ^ 2, s 2 * t 2, t 2 ^ 2] ![s 3 ^ 2, s 3 * t 3, t 3 ^ 2]
      ![s 4 ^ 2, s 4 * t 4, t 4 ^ 2] ![s 5 ^ 2, s 5 * t 5, t 5 ^ 2] = 0 := by
  simp only [pascalDet, cross_apply, vec3_dotProduct, cons_val_zero, cons_val_one, cons_val_two,
    Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons]
  ring

end PascalHexagon
