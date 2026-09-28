import PascalHexagon.Defs
import Mathlib.Tactic.Ring

open Matrix

namespace PascalHexagon

variable {K : Type*} [CommRing K]

/-- The Pascal triple product as a bracket polynomial (any commutative ring, no hypotheses). -/
theorem pascalDet_eq_pascalBracket (A B C D E F : Fin 3 → K) :
    pascalDet A B C D E F = pascalBracket A B C D E F := by
  simp only [pascalDet, pascalBracket, cross_cross_eq_smul_sub_smul, br]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, cross_self,
    dot_self_cross, smul_zero, sub_zero, zero_sub, mul_zero, dotProduct_neg, neg_dotProduct]
  simp only [cross_apply, vec3_dotProduct, cons_val_zero, cons_val_one, cons_val_two,
    Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons]
  ring

end PascalHexagon
