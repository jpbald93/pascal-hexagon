import PascalHexagon.Conic
import Mathlib.LinearAlgebra.Projectivization.Collinear
import Mathlib.LinearAlgebra.Projectivization.Constructions
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Pascal's hexagon theorem in the projective plane `ℙ K (Fin 3 → K)`

* Lines are represented by points of the dual plane (identified with `ℙ K (Fin 3 → K)` via the
  dot product), and `Projectivization.cross` gives both the line through two distinct points
  and the intersection point of two distinct lines.
* A conic is the zero set of a nonzero quadratic form `Q` on `K³`; `Q p.rep = 0` does not depend
  on the chosen representative.
* Collinearity is Mathlib's `Projectivization.IsCollinear`.
-/

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization

namespace PascalHexagon

variable {K : Type*} [Field K]

/-- Three points of `ℙ²` whose representatives have zero triple product are collinear. -/
theorem isCollinear_mk_of_triple_product_eq_zero {u v w : Fin 3 → K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (h : u ⬝ᵥ v ⨯₃ w = 0) :
    IsCollinear ({mk K u hu, mk K v hv, mk K w hw} : Set (ℙ K (Fin 3 → K))) := by
  set s : Submodule K (Fin 3 → K) := Submodule.span K (Set.range ![u, v, w]) with hs
  have hsub : Subspace.submodule s.projectivization = s := OrderIso.apply_symm_apply _ _
  refine ⟨s.projectivization, ?_, ?_, ?_⟩
  · rw [hsub]; infer_instance
  · rw [hsub]
    have hli : ¬ LinearIndependent K ![u, v, w] := by
      intro hli
      have hunit : IsUnit (Matrix.of ![u, v, w]) :=
        (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of ![u, v, w])).mp hli
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
      apply hunit
      have : (Matrix.of ![u, v, w]) = ![u, v, w] := rfl
      rw [this, ← triple_product_eq_det, h]
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank] at hli
    have hle := finrank_range_le_card (R := K) ![u, v, w]
    simp only [Fintype.card_fin] at hli hle
    rw [hs]
    change ¬ Fintype.card (Fin 3) = Module.finrank K (Submodule.span K (Set.range ![u, v, w]))
      at hli
    change Module.finrank K (Submodule.span K (Set.range ![u, v, w])) ≤ 3 at hle
    simp only [Fintype.card_fin] at hli
    omega
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact (Submodule.mk_mem_projectivization_iff s hu).mpr (Submodule.subset_span ⟨0, rfl⟩)
    · exact (Submodule.mk_mem_projectivization_iff s hv).mpr (Submodule.subset_span ⟨1, rfl⟩)
    · exact (Submodule.mk_mem_projectivization_iff s hw).mpr (Submodule.subset_span ⟨2, rfl⟩)

variable [DecidableEq K]

/-- Pascal for projective points given by explicit representatives. -/
theorem pascal_mk {Q : QuadraticForm K (Fin 3 → K)} (hQ : Q ≠ 0) {a b c d e f : Fin 3 → K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hQa : Q a = 0) (hQb : Q b = 0) (hQc : Q c = 0) (hQd : Q d = 0) (hQe : Q e = 0)
    (hQf : Q f = 0)
    (hAB : mk K a ha ≠ mk K b hb) (hBC : mk K b hb ≠ mk K c hc) (hCD : mk K c hc ≠ mk K d hd)
    (hDE : mk K d hd ≠ mk K e he) (hEF : mk K e he ≠ mk K f hf) (hFA : mk K f hf ≠ mk K a ha)
    (h₁ : cross (mk K a ha) (mk K b hb) ≠ cross (mk K d hd) (mk K e he))
    (h₂ : cross (mk K b hb) (mk K c hc) ≠ cross (mk K e he) (mk K f hf))
    (h₃ : cross (mk K c hc) (mk K d hd) ≠ cross (mk K f hf) (mk K a ha)) :
    IsCollinear ({cross (cross (mk K a ha) (mk K b hb)) (cross (mk K d hd) (mk K e he)),
      cross (cross (mk K b hb) (mk K c hc)) (cross (mk K e he) (mk K f hf)),
      cross (cross (mk K c hc) (mk K d hd)) (cross (mk K f hf) (mk K a ha))} :
        Set (ℙ K (Fin 3 → K))) := by
  rw [cross_mk_of_ne ha hb hAB, cross_mk_of_ne hb hc hBC, cross_mk_of_ne hc hd hCD,
    cross_mk_of_ne hd he hDE, cross_mk_of_ne he hf hEF, cross_mk_of_ne hf ha hFA] at *
  rw [cross_mk_of_ne _ _ h₁, cross_mk_of_ne _ _ h₂, cross_mk_of_ne _ _ h₃]
  exact isCollinear_mk_of_triple_product_eq_zero _ _ _
    (pascal_quadraticMap hQ hQa hQb hQc hQd hQe hQf)

/-- **Pascal's hexagon theorem** (projective form, #28 on the "100 theorems" list).

Let `K` be a field and `Q` a nonzero quadratic form on `K³`, so `{p | Q p = 0}` is a
(possibly degenerate) conic in the projective plane `ℙ K (Fin 3 → K)`. Let `A B C D E F` be six
points on the conic such that consecutive vertices are distinct (so the six sides are lines) and
opposite sides are distinct lines (so their intersection is a point). Then the three
intersection points `AB ∩ DE`, `BC ∩ EF`, `CD ∩ FA` are collinear.

No assumptions on the characteristic of `K`, on nondegeneracy of `Q`, or on non-consecutive
vertices being distinct. -/
theorem pascal {Q : QuadraticForm K (Fin 3 → K)} (hQ : Q ≠ 0)
    {A B C D E F : ℙ K (Fin 3 → K)}
    (hQA : Q A.rep = 0) (hQB : Q B.rep = 0) (hQC : Q C.rep = 0) (hQD : Q D.rep = 0)
    (hQE : Q E.rep = 0) (hQF : Q F.rep = 0)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDE : D ≠ E) (hEF : E ≠ F) (hFA : F ≠ A)
    (h₁ : cross A B ≠ cross D E) (h₂ : cross B C ≠ cross E F) (h₃ : cross C D ≠ cross F A) :
    IsCollinear ({cross (cross A B) (cross D E), cross (cross B C) (cross E F),
      cross (cross C D) (cross F A)} : Set (ℙ K (Fin 3 → K))) := by
  have h := pascal_mk hQ A.rep_nonzero B.rep_nonzero C.rep_nonzero D.rep_nonzero E.rep_nonzero
    F.rep_nonzero hQA hQB hQC hQD hQE hQF
    (by simpa only [mk_rep] using hAB) (by simpa only [mk_rep] using hBC)
    (by simpa only [mk_rep] using hCD) (by simpa only [mk_rep] using hDE)
    (by simpa only [mk_rep] using hEF) (by simpa only [mk_rep] using hFA)
    (by simpa only [mk_rep] using h₁) (by simpa only [mk_rep] using h₂)
    (by simpa only [mk_rep] using h₃)
  simpa only [mk_rep] using h

end PascalHexagon
