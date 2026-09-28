import PascalHexagon.Bracket
import PascalHexagon.Veronese
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Pascal's theorem for six points on a conic (vector form)

A conic is the zero set of a homogeneous quadratic polynomial
`a x² + b y² + c z² + d xy + e yz + f zx` with coefficient vector `(a,b,c,d,e,f) ≠ 0`;
equivalently a nonzero `QuadraticForm K (Fin 3 → K)`. No assumption on the characteristic,
no non-degeneracy of the conic, no distinctness of the six points.
-/

open Matrix

namespace PascalHexagon

variable {K : Type*} [CommRing K]

/-- Evaluation of the ternary quadratic form with coefficient vector
`c = (a, b, c, d, e, f)` : `a x² + b y² + c z² + d xy + e yz + f zx`. -/
def quadEval (c : Fin 6 → K) (v : Fin 3 → K) : K := ver v ⬝ᵥ c

/-- **Pascal (polynomial form).** Over an integral domain, six points on the conic
`quadEval c = 0` with nonzero coefficient vector `c` give a vanishing Pascal determinant,
i.e. the three Pascal points are collinear. -/
theorem pascalDet_eq_zero_of_quadEval [IsDomain K] {c : Fin 6 → K} (hc : c ≠ 0)
    {A B C D E F : Fin 3 → K}
    (hA : quadEval c A = 0) (hB : quadEval c B = 0) (hC : quadEval c C = 0)
    (hD : quadEval c D = 0) (hE : quadEval c E = 0) (hF : quadEval c F = 0) :
    pascalDet A B C D E F = 0 := by
  have hdet : (verMatrix A B C D E F).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨c, hc, ?_⟩
    ext i
    fin_cases i <;> assumption
  rw [pascalDet_eq_pascalBracket, ← neg_eq_zero, ← det_verMatrix_eq_neg_pascalBracket, hdet]

/-- Coefficient vector of a quadratic map on `K³`:
`(Q e₀, Q e₁, Q e₂, polar Q e₀ e₁, polar Q e₁ e₂, polar Q e₂ e₀)`. -/
def coeffs (Q : QuadraticMap K (Fin 3 → K) K) : Fin 6 → K :=
  ![Q (Pi.single 0 1), Q (Pi.single 1 1), Q (Pi.single 2 1),
    QuadraticMap.polar Q (Pi.single 0 1) (Pi.single 1 1),
    QuadraticMap.polar Q (Pi.single 1 1) (Pi.single 2 1),
    QuadraticMap.polar Q (Pi.single 2 1) (Pi.single 0 1)]

/-- Every quadratic map on `K³` is the ternary quadratic polynomial with coefficients `coeffs Q`. -/
theorem apply_eq_quadEval (Q : QuadraticMap K (Fin 3 → K) K) (v : Fin 3 → K) :
    Q v = quadEval (coeffs Q) v := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
    ext i; fin_cases i <;> simp
  set e0 : Fin 3 → K := Pi.single 0 1
  set e1 : Fin 3 → K := Pi.single 1 1
  set e2 : Fin 3 → K := Pi.single 2 1
  have h1 : Q (v 0 • e0 + v 1 • e1 + v 2 • e2) =
      Q (v 0 • e0 + v 1 • e1) + Q (v 2 • e2) +
        QuadraticMap.polar Q (v 0 • e0 + v 1 • e1) (v 2 • e2) :=
    QuadraticMap.map_add Q _ _
  have h2 : Q (v 0 • e0 + v 1 • e1) =
      Q (v 0 • e0) + Q (v 1 • e1) + QuadraticMap.polar Q (v 0 • e0) (v 1 • e1) :=
    QuadraticMap.map_add Q _ _
  rw [hv, h1, h2, QuadraticMap.polar_add_left, QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.map_smul, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_comm Q e0 e2]
  have c0 : (v 0 • e0 + v 1 • e1 + v 2 • e2) 0 = v 0 := by simp [e0, e1, e2]
  have c1 : (v 0 • e0 + v 1 • e1 + v 2 • e2) 1 = v 1 := by simp [e0, e1, e2]
  have c2 : (v 0 • e0 + v 1 • e1 + v 2 • e2) 2 = v 2 := by simp [e0, e1, e2]
  simp only [quadEval, ver, coeffs, c0, c1, c2, smul_eq_mul, dotProduct, Fin.sum_univ_succ,
    Fin.sum_univ_zero, cons_val_zero, cons_val_succ, cons_val_one, cons_val_two]
  ring

theorem coeffs_ne_zero {Q : QuadraticMap K (Fin 3 → K) K} (hQ : Q ≠ 0) : coeffs Q ≠ 0 := by
  intro h
  apply hQ
  ext v
  rw [apply_eq_quadEval, h, quadEval, dotProduct_zero, _root_.zero_apply]

/-- **Pascal's hexagon theorem (vector form, general conic).** Let `Q` be a nonzero quadratic
form on `K³` over an integral domain `K` (any characteristic; `Q` may be degenerate, e.g. a
line pair — this case is Pappus). If six vectors `A, …, F` lie on the conic `Q = 0`, then the
three intersection points `(A×B)×(D×E)`, `(B×C)×(E×F)`, `(C×D)×(F×A)` of opposite sides have
zero triple product, i.e. are collinear. No distinctness hypotheses are needed. -/
theorem pascal_quadraticMap [IsDomain K] {Q : QuadraticMap K (Fin 3 → K) K} (hQ : Q ≠ 0)
    {A B C D E F : Fin 3 → K}
    (hA : Q A = 0) (hB : Q B = 0) (hC : Q C = 0) (hD : Q D = 0) (hE : Q E = 0) (hF : Q F = 0) :
    ((A ⨯₃ B) ⨯₃ (D ⨯₃ E)) ⬝ᵥ ((B ⨯₃ C) ⨯₃ (E ⨯₃ F)) ⨯₃ ((C ⨯₃ D) ⨯₃ (F ⨯₃ A)) = 0 := by
  simp only [apply_eq_quadEval Q] at hA hB hC hD hE hF
  exact pascalDet_eq_zero_of_quadEval (coeffs_ne_zero hQ) hA hB hC hD hE hF

/-- Same, with the conclusion phrased as a vanishing 3×3 determinant. -/
theorem pascal_quadraticMap_det [IsDomain K] {Q : QuadraticMap K (Fin 3 → K) K} (hQ : Q ≠ 0)
    {A B C D E F : Fin 3 → K}
    (hA : Q A = 0) (hB : Q B = 0) (hC : Q C = 0) (hD : Q D = 0) (hE : Q E = 0) (hF : Q F = 0) :
    Matrix.det ![(A ⨯₃ B) ⨯₃ (D ⨯₃ E), (B ⨯₃ C) ⨯₃ (E ⨯₃ F), (C ⨯₃ D) ⨯₃ (F ⨯₃ A)] = 0 := by
  rw [← triple_product_eq_det]
  exact pascal_quadraticMap hQ hA hB hC hD hE hF

/-- Symmetric-matrix version: points with `vᵀ M v = 0` for a symmetric `M ≠ 0`, in
characteristic `≠ 2` (needed: for char 2, `vᵀ M v` only sees the diagonal of `M`). -/
theorem pascal_matrix {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M ≠ 0) (hMsymm : M.IsSymm) {A B C D E F : Fin 3 → K}
    (hA : A ⬝ᵥ M *ᵥ A = 0) (hB : B ⬝ᵥ M *ᵥ B = 0) (hC : C ⬝ᵥ M *ᵥ C = 0)
    (hD : D ⬝ᵥ M *ᵥ D = 0) (hE : E ⬝ᵥ M *ᵥ E = 0) (hF : F ⬝ᵥ M *ᵥ F = 0) :
    pascalDet A B C D E F = 0 := by
  let c : Fin 6 → K := ![M 0 0, M 1 1, M 2 2, 2 * M 0 1, 2 * M 1 2, 2 * M 2 0]
  have key : ∀ v : Fin 3 → K, v ⬝ᵥ M *ᵥ v = quadEval c v := by
    intro v
    have h10 : M 1 0 = M 0 1 := hMsymm.apply 0 1
    have h21 : M 2 1 = M 1 2 := hMsymm.apply 1 2
    have h02 : M 0 2 = M 2 0 := hMsymm.apply 2 0
    simp only [quadEval, ver, c, dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero,
      cons_val_zero, cons_val_succ, cons_val_one, cons_val_two, h10, h21, h02]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    simp only [h10, h21, h02]
    ring
  have hc : c ≠ 0 := by
    intro h
    apply hM
    have e : ∀ i : Fin 6, c i = 0 := fun i => by rw [h]; rfl
    have m00 : M 0 0 = 0 := by simpa [c] using e 0
    have m11 : M 1 1 = 0 := by simpa [c] using e 1
    have m22 : M 2 2 = 0 := by simpa [c] using e 2
    have m01 : M 0 1 = 0 := by simpa [c, h2] using e 3
    have m12 : M 1 2 = 0 := by simpa [c, h2] using e 4
    have m20 : M 2 0 = 0 := by simpa [c, h2] using e 5
    have m10 : M 1 0 = 0 := (hMsymm.apply 0 1).trans m01
    have m21 : M 2 1 = 0 := (hMsymm.apply 1 2).trans m12
    have m02 : M 0 2 = 0 := (hMsymm.apply 2 0).trans m20
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m00, m11, m22, m01, m12, m20, m10, m21, m02]
  rw [key] at hA hB hC hD hE hF
  exact pascalDet_eq_zero_of_quadEval hc hA hB hC hD hE hF

end PascalHexagon
