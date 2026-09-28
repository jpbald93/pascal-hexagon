import PascalHexagon.Correctness

/-!
# Brianchon's theorem

Brianchon's theorem is the projective dual of Pascal's theorem. Let `a, b, c, d, e, f` be six lines
lying on a conic in the dual plane. (Classically, for a nonsingular conic over a field of
characteristic different from two, these are exactly the six tangent lines to that conic.) Suppose
consecutive sides are distinct lines and opposite vertices are distinct points. Then the three
diagonals, joining opposite vertices, are collinear as points of the dual plane.

In `ℙ K (Fin 3 → K)`, lines are identified with points via the dot product, and
`Projectivization.cross` computes both the join of two points and the meet of two lines.
Duality is therefore literal. We state membership of the dual conic as `OnConic Q' ℓ` for a nonzero
quadratic form `Q'`, so that Brianchon's theorem is Pascal's theorem applied to `Q'`. For arbitrary
`Q'` this is a dual-Pascal generalisation; no tangent interpretation is asserted.

* the vertices of the hexagon of lines are `cross a b, cross b c, …`;
* the diagonal joining the opposite vertices `a ∩ b` and `d ∩ e` is `cross (cross a b) (cross d e)`;
* three lines are concurrent iff, as points of the dual plane, they are collinear.

We also state concurrency in the form "there is a point on all three diagonals" and prove it from
Pascal together with the incidence lemmas of `Correctness.lean`.
-/

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization

namespace PascalHexagon

variable {K : Type*} [Field K] [DecidableEq K]

/-- **Brianchon's theorem** (dual form). Let `a, b, c, d, e, f` be six lines lying on a nonzero
dual conic `Q` (classically, tangent to the corresponding conic). Suppose consecutive sides are
distinct and opposite vertices `a ∩ b, d ∩ e` (and so on) are distinct points. Then the three
diagonals `(a∩b)(d∩e)`, `(b∩c)(e∩f)` and `(c∩d)(f∩a)` are collinear as points of the dual plane,
that is, concurrent as lines. This is `pascal` read in the dual plane. -/
theorem brianchon {Q : QuadraticForm K (Fin 3 → K)} (hQ : Q ≠ 0)
    {a b c d e f : ℙ K (Fin 3 → K)}
    (ha : OnConic Q a) (hb : OnConic Q b) (hc : OnConic Q c) (hd : OnConic Q d)
    (he : OnConic Q e) (hf : OnConic Q f)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f) (hfa : f ≠ a)
    (h₁ : cross a b ≠ cross d e) (h₂ : cross b c ≠ cross e f) (h₃ : cross c d ≠ cross f a) :
    IsCollinear ({cross (cross a b) (cross d e), cross (cross b c) (cross e f),
      cross (cross c d) (cross f a)} : Set (ℙ K (Fin 3 → K))) :=
  pascal' hQ ha hb hc hd he hf hab hbc hcd hde hef hfa h₁ h₂ h₃

/-- Three lines `L, M, N` with `L ≠ M` whose points in the dual plane are collinear pass through
a common point. -/
theorem exists_common_point_of_isCollinear {L M N : ℙ K (Fin 3 → K)} (hLM : L ≠ M)
    (h : IsCollinear ({L, M, N} : Set (ℙ K (Fin 3 → K)))) :
    ∃ X : ℙ K (Fin 3 → K), X.orthogonal L ∧ X.orthogonal M ∧ X.orthogonal N := by
  refine ⟨cross L M, (cross_mem_lines hLM).1, (cross_mem_lines hLM).2, ?_⟩
  have hN : N.orthogonal (cross L M) := (orthogonal_cross_iff_isCollinear hLM).mpr h
  exact orthogonal_comm.mp hN

/-- **Brianchon's theorem** (concurrency form). Under the hypotheses of `brianchon`, if the first
two diagonals are distinct lines, some point lies on all three diagonals. The distinctness of the
first two diagonals is needed only by the explicit cross-product witness; as points of the dual
plane, collinear points always have a common point when at least two are distinct. -/
theorem brianchon_concurrent {Q : QuadraticForm K (Fin 3 → K)} (hQ : Q ≠ 0)
    {a b c d e f : ℙ K (Fin 3 → K)}
    (ha : OnConic Q a) (hb : OnConic Q b) (hc : OnConic Q c) (hd : OnConic Q d)
    (he : OnConic Q e) (hf : OnConic Q f)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f) (hfa : f ≠ a)
    (h₁ : cross a b ≠ cross d e) (h₂ : cross b c ≠ cross e f) (h₃ : cross c d ≠ cross f a)
    (h₁₂ : cross (cross a b) (cross d e) ≠ cross (cross b c) (cross e f)) :
    ∃ X : ℙ K (Fin 3 → K), X.orthogonal (cross (cross a b) (cross d e)) ∧
      X.orthogonal (cross (cross b c) (cross e f)) ∧
      X.orthogonal (cross (cross c d) (cross f a)) :=
  exists_common_point_of_isCollinear h₁₂
    (brianchon hQ ha hb hc hd he hf hab hbc hcd hde hef hfa h₁ h₂ h₃)

end PascalHexagon
