import PascalHexagon.Projective

/-!
# Sanity lemmas for the statement of `PascalHexagon.pascal`

This file justifies the formal statement of Pascal's theorem.

* **Incidence.** For a point `P` and a line `L` (a point of the dual plane, identified with
  `ℙ K (Fin 3 → K)` by the dot product), "`P` lies on `L`" is `P.orthogonal L`.
  * `cross A B` is the unique line through two distinct points `A` and `B`.
  * `cross L M` is the unique point on two distinct lines `L` and `M`.
  So the three points in the conclusion of `pascal` are exactly `AB ∩ DE`, `BC ∩ EF` and
  `CD ∩ FA`.
* **Collinearity.** `IsCollinear {mk u, mk v, mk w} ↔ u ⬝ᵥ v ⨯₃ w = 0`. As a consequence, for
  `A ≠ B`, `IsCollinear {A, B, P} ↔ P` lies on `cross A B`. This gives `pascal_of_isCollinear`,
  in which the three Pascal points are arbitrary points specified only through Mathlib's
  `IsCollinear`.
* **Conics.** `OnConic Q P` is independent of the representative of `P`, and `pascal'` is
  `pascal` stated with it.
* **Pappus.** A product of two nonzero linear forms is a nonzero quadratic form, so Pascal's
  theorem for this degenerate conic gives Pappus's theorem (`pappus`).
-/

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization

namespace PascalHexagon

variable {K : Type*} [Field K]

/-! ### Collinearity and the triple product -/

/-- Converse of `isCollinear_mk_of_triple_product_eq_zero`. -/
theorem triple_product_eq_zero_of_isCollinear_mk {u v w : Fin 3 → K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : IsCollinear ({mk K u hu, mk K v hv, mk K w hw} : Set (ℙ K (Fin 3 → K)))) :
    u ⬝ᵥ v ⨯₃ w = 0 := by
  obtain ⟨M, hfin, hrank, hsub⟩ := h
  by_contra hne
  have hli : LinearIndependent K ![u, v, w] := by
    have hunit : IsUnit (Matrix.of ![u, v, w]) := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      have : (Matrix.of ![u, v, w]) = ![u, v, w] := rfl
      rw [this, ← triple_product_eq_det]
      exact hne
    exact (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of ![u, v, w])).mpr hunit
  have hmem : ∀ (x : Fin 3 → K) (hx : x ≠ 0),
      mk K x hx ∈ ({mk K u hu, mk K v hv, mk K w hw} : Set (ℙ K (Fin 3 → K))) →
        x ∈ M.submodule := fun x hx hS => (Subspace.mem_submodule_iff M hx).mpr (hsub hS)
  have hle : Submodule.span K (Set.range ![u, v, w]) ≤ M.submodule := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hmem u hu (by simp)
    · exact hmem v hv (by simp)
    · exact hmem w hw (by simp)
  have h3 := finrank_span_eq_card hli
  have hmono := Submodule.finrank_mono hle
  simp only [Fintype.card_fin] at h3
  omega

/-- Three points of `ℙ²` given by representatives are collinear iff the triple product of the
representatives vanishes. -/
theorem isCollinear_mk_iff {u v w : Fin 3 → K} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    IsCollinear ({mk K u hu, mk K v hv, mk K w hw} : Set (ℙ K (Fin 3 → K))) ↔
      u ⬝ᵥ v ⨯₃ w = 0 :=
  ⟨triple_product_eq_zero_of_isCollinear_mk hu hv hw,
    isCollinear_mk_of_triple_product_eq_zero hu hv hw⟩

/-- Representative-free form: `A, B, C` are collinear iff `det [A.rep, B.rep, C.rep] = 0`
(for any choice of representatives, in particular `rep`). -/
theorem isCollinear_iff_det_rep (A B C : ℙ K (Fin 3 → K)) :
    IsCollinear ({A, B, C} : Set (ℙ K (Fin 3 → K))) ↔
      Matrix.det ![A.rep, B.rep, C.rep] = 0 := by
  have h := isCollinear_mk_iff A.rep_nonzero B.rep_nonzero C.rep_nonzero
  rw [mk_rep, mk_rep, mk_rep, triple_product_eq_det] at h
  exact h

/-! ### Incidence of points and lines -/

/-- Incidence on representatives: `P` lies on `L` iff `P.rep ⬝ᵥ L.rep = 0`. -/
theorem orthogonal_iff_rep (P L : ℙ K (Fin 3 → K)) :
    P.orthogonal L ↔ P.rep ⬝ᵥ L.rep = 0 := by
  have h := orthogonal_mk P.rep_nonzero L.rep_nonzero
  rw [mk_rep, mk_rep] at h
  exact h

variable [DecidableEq K]

/-- The line `cross A B` passes through both `A` and `B` (for `A ≠ B`). -/
theorem mem_line_cross {A B : ℙ K (Fin 3 → K)} (h : A ≠ B) :
    A.orthogonal (cross A B) ∧ B.orthogonal (cross A B) :=
  ⟨orthogonal_cross_left h, orthogonal_cross_right h⟩

/-- The point `cross L M` lies on both lines `L` and `M` (for `L ≠ M`). -/
theorem cross_mem_lines {L M : ℙ K (Fin 3 → K)} (h : L ≠ M) :
    (cross L M).orthogonal L ∧ (cross L M).orthogonal M :=
  ⟨cross_orthogonal_left h, cross_orthogonal_right h⟩

/-- Uniqueness of the intersection point: a point on two distinct lines `L ≠ M` is
`cross L M`. -/
theorem eq_cross_of_orthogonal {L M P : ℙ K (Fin 3 → K)} (hLM : L ≠ M)
    (hL : P.orthogonal L) (hM : P.orthogonal M) : P = cross L M := by
  induction L using Projectivization.ind with | h l hl =>
  induction M using Projectivization.ind with | h m hm =>
  induction P using Projectivization.ind with | h p hp =>
  rw [orthogonal_mk] at hL hM
  rw [cross_mk_of_ne hl hm hLM, mk_eq_mk_iff_crossProduct_eq_zero,
    cross_cross_eq_smul_sub_smul', hM, dotProduct_comm l p, hL, zero_smul, zero_smul, sub_zero]

/-- Uniqueness of the line: a line through two distinct points `A ≠ B` is `cross A B`. -/
theorem eq_cross_of_orthogonal' {A B L : ℙ K (Fin 3 → K)} (hAB : A ≠ B)
    (hA : A.orthogonal L) (hB : B.orthogonal L) : L = cross A B :=
  eq_cross_of_orthogonal hAB (orthogonal_comm.mp hA) (orthogonal_comm.mp hB)

/-- A point `P` lies on the line `cross A B` iff `A, B, P` are collinear (for `A ≠ B`). -/
theorem orthogonal_cross_iff_isCollinear {A B P : ℙ K (Fin 3 → K)} (hAB : A ≠ B) :
    P.orthogonal (cross A B) ↔ IsCollinear ({A, B, P} : Set (ℙ K (Fin 3 → K))) := by
  induction A using Projectivization.ind with | h a ha =>
  induction B using Projectivization.ind with | h b hb =>
  induction P using Projectivization.ind with | h p hp =>
  rw [cross_mk_of_ne ha hb hAB, orthogonal_mk, isCollinear_mk_iff,
    triple_product_permutation a b p, triple_product_permutation b p a]

/-- Characterisation of the intersection point of two distinct lines `AB ≠ DE`. The point
`cross (cross A B) (cross D E)` is collinear with `A, B` and with `D, E`, and it is the only such
point. -/
theorem cross_cross_spec {A B D E : ℙ K (Fin 3 → K)} (hAB : A ≠ B) (hDE : D ≠ E)
    (h : cross A B ≠ cross D E) :
    IsCollinear ({A, B, cross (cross A B) (cross D E)} : Set (ℙ K (Fin 3 → K))) ∧
    IsCollinear ({D, E, cross (cross A B) (cross D E)} : Set (ℙ K (Fin 3 → K))) ∧
    ∀ X : ℙ K (Fin 3 → K), IsCollinear ({A, B, X} : Set (ℙ K (Fin 3 → K))) →
      IsCollinear ({D, E, X} : Set (ℙ K (Fin 3 → K))) → X = cross (cross A B) (cross D E) := by
  refine ⟨(orthogonal_cross_iff_isCollinear hAB).mp (cross_orthogonal_left h),
    (orthogonal_cross_iff_isCollinear hDE).mp (cross_orthogonal_right h), fun X h₁ h₂ => ?_⟩
  exact eq_cross_of_orthogonal h ((orthogonal_cross_iff_isCollinear hAB).mpr h₁)
    ((orthogonal_cross_iff_isCollinear hDE).mpr h₂)

/-! ### Points on a conic -/

/-- The projective point `P` lies on the conic `Q = 0`. -/
def OnConic (Q : QuadraticForm K (Fin 3 → K)) (P : ℙ K (Fin 3 → K)) : Prop := Q P.rep = 0

omit [DecidableEq K] in
/-- `OnConic` does not depend on the choice of representative. -/
theorem onConic_mk_iff (Q : QuadraticForm K (Fin 3 → K)) {v : Fin 3 → K} (hv : v ≠ 0) :
    OnConic Q (mk K v hv) ↔ Q v = 0 := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
  unfold OnConic
  rw [← ha, Units.smul_def, QuadraticMap.map_smul, smul_eq_mul,
    mul_eq_zero_iff_left (mul_ne_zero a.ne_zero a.ne_zero)]

/-- **Pascal's hexagon theorem**, stated with `OnConic`. This is `pascal` with the conic
hypotheses written in representative-independent form. -/
theorem pascal' {Q : QuadraticForm K (Fin 3 → K)} (hQ : Q ≠ 0)
    {A B C D E F : ℙ K (Fin 3 → K)}
    (hA : OnConic Q A) (hB : OnConic Q B) (hC : OnConic Q C) (hD : OnConic Q D)
    (hE : OnConic Q E) (hF : OnConic Q F)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDE : D ≠ E) (hEF : E ≠ F) (hFA : F ≠ A)
    (h₁ : cross A B ≠ cross D E) (h₂ : cross B C ≠ cross E F) (h₃ : cross C D ≠ cross F A) :
    IsCollinear ({cross (cross A B) (cross D E), cross (cross B C) (cross E F),
      cross (cross C D) (cross F A)} : Set (ℙ K (Fin 3 → K))) :=
  pascal hQ hA hB hC hD hE hF hAB hBC hCD hDE hEF hFA h₁ h₂ h₃

/-- **Pascal's hexagon theorem** with the three intersection points `P, R, S` given as arbitrary
points specified by collinearity conditions in Mathlib's `IsCollinear`: `P ∈ AB ∩ DE`,
`R ∈ BC ∩ EF` and `S ∈ CD ∩ FA`. -/
theorem pascal_of_isCollinear {Q : QuadraticForm K (Fin 3 → K)} (hQ : Q ≠ 0)
    {A B C D E F P R S : ℙ K (Fin 3 → K)}
    (hA : OnConic Q A) (hB : OnConic Q B) (hC : OnConic Q C) (hD : OnConic Q D)
    (hE : OnConic Q E) (hF : OnConic Q F)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDE : D ≠ E) (hEF : E ≠ F) (hFA : F ≠ A)
    (h₁ : cross A B ≠ cross D E) (h₂ : cross B C ≠ cross E F) (h₃ : cross C D ≠ cross F A)
    (hP₁ : IsCollinear ({A, B, P} : Set (ℙ K (Fin 3 → K))))
    (hP₂ : IsCollinear ({D, E, P} : Set (ℙ K (Fin 3 → K))))
    (hR₁ : IsCollinear ({B, C, R} : Set (ℙ K (Fin 3 → K))))
    (hR₂ : IsCollinear ({E, F, R} : Set (ℙ K (Fin 3 → K))))
    (hS₁ : IsCollinear ({C, D, S} : Set (ℙ K (Fin 3 → K))))
    (hS₂ : IsCollinear ({F, A, S} : Set (ℙ K (Fin 3 → K)))) :
    IsCollinear ({P, R, S} : Set (ℙ K (Fin 3 → K))) := by
  rw [(cross_cross_spec hAB hDE h₁).2.2 P hP₁ hP₂, (cross_cross_spec hBC hEF h₂).2.2 R hR₁ hR₂,
    (cross_cross_spec hCD hFA h₃).2.2 S hS₁ hS₂]
  exact pascal' hQ hA hB hC hD hE hF hAB hBC hCD hDE hEF hFA h₁ h₂ h₃

/-! ### Pappus as a degenerate Pascal -/

omit [DecidableEq K] in
/-- The linear form `v ↦ a ⬝ᵥ v`. -/
def dotLeft (a : Fin 3 → K) : (Fin 3 → K) →ₗ[K] K where
  toFun v := a ⬝ᵥ v
  map_add' v w := dotProduct_add a v w
  map_smul' c v := dotProduct_smul c a v

omit [DecidableEq K] in
/-- The line pair `(a ⬝ᵥ x) * (b ⬝ᵥ x) = 0`, a degenerate conic. -/
def linePair (a b : Fin 3 → K) : QuadraticForm K (Fin 3 → K) :=
  QuadraticMap.linMulLin (dotLeft a) (dotLeft b)

omit [DecidableEq K] in
theorem linePair_apply (a b x : Fin 3 → K) : linePair a b x = (a ⬝ᵥ x) * (b ⬝ᵥ x) := rfl

omit [DecidableEq K] in
/-- A product of two nonzero linear forms is a nonzero quadratic form. -/
theorem linePair_ne_zero {a b : Fin 3 → K} (ha : a ≠ 0) (hb : b ≠ 0) : linePair a b ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, a ⬝ᵥ x ≠ 0 := by
    by_contra h; push Not at h; exact ha (dotProduct_eq_zero_iff.mp h)
  obtain ⟨y, hy⟩ : ∃ y, b ⬝ᵥ y ≠ 0 := by
    by_contra h; push Not at h; exact hb (dotProduct_eq_zero_iff.mp h)
  -- a witness `z` with `a ⬝ᵥ z ≠ 0` and `b ⬝ᵥ z ≠ 0`
  obtain ⟨z, hza, hzb⟩ : ∃ z, a ⬝ᵥ z ≠ 0 ∧ b ⬝ᵥ z ≠ 0 := by
    by_cases hbx : b ⬝ᵥ x = 0
    · by_cases hay : a ⬝ᵥ y = 0
      · refine ⟨x + y, ?_, ?_⟩
        · rw [dotProduct_add, hay, add_zero]; exact hx
        · rw [dotProduct_add, hbx, zero_add]; exact hy
      · exact ⟨y, hay, hy⟩
    · exact ⟨x, hx, hbx⟩
  intro h
  have := congrArg (fun q : QuadraticForm K (Fin 3 → K) => q z) h
  simp only [linePair_apply, _root_.zero_apply] at this
  exact mul_ne_zero hza hzb this

omit [DecidableEq K] in
/-- A point on the line `a` (or on the line `b`) lies on the line pair `linePair a.rep b.rep`. -/
theorem onConic_linePair {a b P : ℙ K (Fin 3 → K)} (h : P.orthogonal a ∨ P.orthogonal b) :
    OnConic (linePair a.rep b.rep) P := by
  unfold OnConic
  rw [linePair_apply]
  rcases h with h | h
  · rw [orthogonal_iff_rep, dotProduct_comm] at h; rw [h, zero_mul]
  · rw [orthogonal_iff_rep, dotProduct_comm] at h; rw [h, mul_zero]

/-- **Pappus's hexagon theorem** (projective form), as the line-pair case of Pascal. Suppose
`A, C, E` lie on the line `a` and `B, D, F` lie on the line `b`, consecutive vertices are distinct
and opposite sides are distinct. Then `AB ∩ DE`, `BC ∩ EF` and `CD ∩ FA` are collinear. -/
theorem pappus {a b A B C D E F : ℙ K (Fin 3 → K)}
    (hA : A.orthogonal a) (hC : C.orthogonal a) (hE : E.orthogonal a)
    (hB : B.orthogonal b) (hD : D.orthogonal b) (hF : F.orthogonal b)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDE : D ≠ E) (hEF : E ≠ F) (hFA : F ≠ A)
    (h₁ : cross A B ≠ cross D E) (h₂ : cross B C ≠ cross E F) (h₃ : cross C D ≠ cross F A) :
    IsCollinear ({cross (cross A B) (cross D E), cross (cross B C) (cross E F),
      cross (cross C D) (cross F A)} : Set (ℙ K (Fin 3 → K))) :=
  pascal' (linePair_ne_zero a.rep_nonzero b.rep_nonzero)
    (onConic_linePair (Or.inl hA)) (onConic_linePair (Or.inr hB)) (onConic_linePair (Or.inl hC))
    (onConic_linePair (Or.inr hD)) (onConic_linePair (Or.inl hE)) (onConic_linePair (Or.inr hF))
    hAB hBC hCD hDE hEF hFA h₁ h₂ h₃

end PascalHexagon
