# Pascal's hexagon theorem in Lean 4 + Mathlib: feasibility spike report

Toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1` (prebuilt oleans). About 1 hour of work.
Nothing has been committed or pushed.

**Summary.** All three stages are **proved, with no `sorry`**. `lake build` succeeds on the whole
library. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

The key step is a single polynomial identity: `pascalDet = −det(Veronese 6×6)`. It holds over
any commutative ring and needs no hypotheses. Stage 2 therefore needs no change of coordinates
and no classification of conics. It holds in any characteristic, for degenerate conics
(line pairs, i.e. Pappus, and double lines), with no distinctness assumptions.

> ⚠️ **Prior art (see §5).** There are already Lean 4 formalisations of #28 on GitHub, but none
> is in Mathlib:
> * **`plby/lean-proofs`**: a sorry-free proof (Aristotle/Harmonic), but **for circles in the
>   Euclidean plane ℝ²** only.
> * **`rjwalters/lean-genius`**: a projective version over ℝ whose main theorem rests on an
>   **`axiom`**. Its axiom-free parts cover only the standard conic and the symmetric
>   non-degenerate real case.
> * **`facebookresearch/atlas-lean`**: a Bézout/Cayley–Bacharach route. It has several
>   `sorry`s and assumes `IsAlgClosed`.
>
> As far as I can tell, nothing public has the general statement proved here: any field, any
> nonzero quadratic form, stated with Mathlib's `Projectivization` and `IsCollinear`, and free
> of both axioms and sorry.

---

## 1. Statements proved (file:line)

All declarations are in `namespace PascalHexagon`. `PascalHexagon.lean` imports every module.

Definitions (`PascalHexagon/Defs.lean`):
```lean
def br (u v w : Fin 3 → K) : K := u ⬝ᵥ v ⨯₃ w                                   -- :23
def pascalBracket (A B C D E F : Fin 3 → K) : K :=                              -- :26
  br A B E * br B C F * br C D A * br D E F - br A B E * br B C F * br C D F * br D E A
    + br A B E * br B C E * br C D F * br D F A - br A B D * br B C E * br C D F * br E F A
def pascalDet (A B C D E F : Fin 3 → K) : K :=                                  -- :31
  ((A ⨯₃ B) ⨯₃ (D ⨯₃ E)) ⬝ᵥ ((B ⨯₃ C) ⨯₃ (E ⨯₃ F)) ⨯₃ ((C ⨯₃ D) ⨯₃ (F ⨯₃ A))
def ver (v : Fin 3 → K) : Fin 6 → K :=                                          -- :35
  ![v 0 ^ 2, v 1 ^ 2, v 2 ^ 2, v 0 * v 1, v 1 * v 2, v 2 * v 0]
def verMatrix (A B C D E F : Fin 3 → K) : Matrix (Fin 6) (Fin 6) K :=           -- :39
  Matrix.of ![ver A, ver B, ver C, ver D, ver E, ver F]
```

### Stage 1: standard conic `xz = y²` (`[CommRing K]`)
`PascalHexagon/StandardConic.lean:17`
```lean
theorem pascalDet_standardConic (s t : Fin 6 → K) :
    pascalDet ![s 0 ^ 2, s 0 * t 0, t 0 ^ 2] ![s 1 ^ 2, s 1 * t 1, t 1 ^ 2]
      ![s 2 ^ 2, s 2 * t 2, t 2 ^ 2] ![s 3 ^ 2, s 3 * t 3, t 3 ^ 2]
      ![s 4 ^ 2, s 4 * t 4, t 4 ^ 2] ![s 5 ^ 2, s 5 * t 5, t 5 ^ 2] = 0
```
The proof is `simp only [cross_apply, vec3_dotProduct, …]; ring`. It takes about 25 s and 2.4 GB.

### Core identities (`[CommRing K]`, no hypotheses)
`PascalHexagon/Bracket.lean:11`
```lean
theorem pascalDet_eq_pascalBracket (A B C D E F : Fin 3 → K) :
    pascalDet A B C D E F = pascalBracket A B C D E F
```
The proof applies `cross_cross_eq_smul_sub_smul` symbolically (collapsing the double crosses into
brackets), then expands coordinates and runs `ring`. About 80 s and 2.6 GB.

`PascalHexagon/Veronese.lean:12`
```lean
theorem det_verMatrix_eq_neg_pascalBracket (A B C D E F : Fin 3 → K) :
    (verMatrix A B C D E F).det = -pascalBracket A B C D E F
```
The proof is Laplace expansion (`det_succ_row_zero`, `Fin.sum_univ_succ`, `Fin.succAbove`) followed
by `ring`. About 95 s and 2.4 GB. Together with the previous lemma this gives the 720-term
identity `pascalDet = −det verMatrix`. I first confirmed it in sympy: the quotient is exactly −1.

### Stage 2: general conic
`PascalHexagon/Conic.lean`
```lean
def quadEval (c : Fin 6 → K) (v : Fin 3 → K) : K := ver v ⬝ᵥ c                 -- :23

-- :28   [CommRing K] [IsDomain K]
theorem pascalDet_eq_zero_of_quadEval [IsDomain K] {c : Fin 6 → K} (hc : c ≠ 0)
    {A B C D E F : Fin 3 → K}
    (hA : quadEval c A = 0) (hB : quadEval c B = 0) (hC : quadEval c C = 0)
    (hD : quadEval c D = 0) (hE : quadEval c E = 0) (hF : quadEval c F = 0) :
    pascalDet A B C D E F = 0

-- :49   every quadratic map on K³ is a ternary quadratic polynomial
theorem apply_eq_quadEval (Q : QuadraticMap K (Fin 3 → K) K) (v : Fin 3 → K) :
    Q v = quadEval (coeffs Q) v
-- :75
theorem coeffs_ne_zero {Q : QuadraticMap K (Fin 3 → K) K} (hQ : Q ≠ 0) : coeffs Q ≠ 0

-- :86   MAIN VECTOR FORM
theorem pascal_quadraticMap [IsDomain K] {Q : QuadraticMap K (Fin 3 → K) K} (hQ : Q ≠ 0)
    {A B C D E F : Fin 3 → K}
    (hA : Q A = 0) (hB : Q B = 0) (hC : Q C = 0) (hD : Q D = 0) (hE : Q E = 0) (hF : Q F = 0) :
    ((A ⨯₃ B) ⨯₃ (D ⨯₃ E)) ⬝ᵥ ((B ⨯₃ C) ⨯₃ (E ⨯₃ F)) ⨯₃ ((C ⨯₃ D) ⨯₃ (F ⨯₃ A)) = 0
-- :94   same, with conclusion  Matrix.det ![P, Q, R] = 0
theorem pascal_quadraticMap_det …
-- :103  symmetric-matrix version
theorem pascal_matrix {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M ≠ 0) (hMsymm : M.IsSymm) {A B C D E F : Fin 3 → K}
    (hA : A ⬝ᵥ M *ᵥ A = 0) … (hF : F ⬝ᵥ M *ᵥ F = 0) :
    pascalDet A B C D E F = 0
```
How `pascalDet_eq_zero_of_quadEval` works: `verMatrix *ᵥ c = 0` with `c ≠ 0`, so
`det verMatrix = 0` by `Matrix.exists_mulVec_eq_zero_iff`. The core identity then finishes it.

**Which hypotheses are actually needed.**
- **Integral domain:** needed only for "a nonzero kernel vector ⇒ det = 0".
- **`c ≠ 0` (equivalently `Q ≠ 0`):** needed, since otherwise every point is "on the conic".
- **Not needed:** characteristic ≠ 2, non-degeneracy, and distinct points.
- **The matrix version is different.** It needs `2 ≠ 0`. In characteristic 2, `vᵀMv` ignores the
  off-diagonal entries of `M`, so a nonzero symmetric `M` can give the zero form. `QuadraticForm`
  is the right primitive.

### Stage 3: projective statement (`[Field K] [DecidableEq K]`)
`PascalHexagon/Projective.lean`
```lean
-- :28
theorem isCollinear_mk_of_triple_product_eq_zero {u v w : Fin 3 → K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (h : u ⬝ᵥ v ⨯₃ w = 0) :
    IsCollinear ({mk K u hu, mk K v hv, mk K w hw} : Set (ℙ K (Fin 3 → K)))
-- :63  pascal_mk: same as below but with explicit representatives
-- :92  MAIN THEOREM
theorem pascal {Q : QuadraticForm K (Fin 3 → K)} (hQ : Q ≠ 0)
    {A B C D E F : ℙ K (Fin 3 → K)}
    (hQA : Q A.rep = 0) (hQB : Q B.rep = 0) (hQC : Q C.rep = 0) (hQD : Q D.rep = 0)
    (hQE : Q E.rep = 0) (hQF : Q F.rep = 0)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDE : D ≠ E) (hEF : E ≠ F) (hFA : F ≠ A)
    (h₁ : cross A B ≠ cross D E) (h₂ : cross B C ≠ cross E F) (h₃ : cross C D ≠ cross F A) :
    IsCollinear ({cross (cross A B) (cross D E), cross (cross B C) (cross E F),
      cross (cross C D) (cross F A)} : Set (ℙ K (Fin 3 → K)))
```
- `Projectivization.cross` is Mathlib's cross product on ℙ² (`Constructions.lean`). It gives both
  the line through two points (as a point of the dual plane, identified via the dot product) and
  the meet of two lines.
- `IsCollinear` is Mathlib's `Projectivization.IsCollinear`.
- The six distinctness hypotheses make sure `cross` means "the line through" and "the
  intersection point". Mathlib's `cross v v := v` convention would otherwise produce junk.

## 2. `#print axioms`
Run from a temporary file that imports `PascalHexagon` (since deleted):
```
'PascalHexagon.pascalDet_standardConic' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.pascalDet_eq_pascalBracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.det_verMatrix_eq_neg_pascalBracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.pascalDet_eq_zero_of_quadEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.apply_eq_quadEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.pascal_quadraticMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.pascal_quadraticMap_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.pascal_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.isCollinear_mk_of_triple_product_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.pascal_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'PascalHexagon.pascal' depends on axioms: [propext, Classical.choice, Quot.sound]
```
I scanned all sources for the forbidden tokens (`sorry|admit|native_decide|axiom|#eval|run_cmd|set_option|macro|elab|syntax|notation|import Lean`) and found **no matches**.

## 3. What is still missing for a Mathlib-quality statement
1. **Conic membership uses `Q A.rep = 0`.** It is independent of the representative (Q(a·v) = a²Q(v)),
   but this is not yet packaged. The Mathlib-style version would be a predicate or set
   `Q.projZeroSet : Set (ℙ K V)` defined via `Quotient.lift`, with a `mk` lemma. This is easy,
   about 20 lines.
2. **Lines are encoded as dual points via `cross`.** Mathlib has no "line" type for ℙ² apart from
   `Projectivization.Subspace` with finrank 2. A reviewer might want the hypotheses phrased as
   Mathlib's `pascal_hexagon` in `docs/100.yaml` style: "P ∈ line AB ∧ P ∈ line DE" using
   `Subspace.span {A, B}`, or through `IsCollinear {A, B, P}`. A version with the auxiliary points
   `P Q R` as hypotheses ("`IsCollinear {A,B,P}`, `IsCollinear {D,E,P}`, …") needs a lemma
   linking `IsCollinear {a, b, c} ↔ det = 0`. The ← direction is done
   (`isCollinear_mk_of_triple_product_eq_zero`); the → direction needs roughly 40–80 lines.
   The theorem also needs uniqueness of the intersection point, which follows from the
   distinctness hypotheses.
3. **Degenerate cases.** The vector form (`pascal_quadraticMap`) covers every case, as a statement
   about the vectors `(A×B)×(D×E)` and so on, which may be zero. The projective form assumes
   consecutive vertices distinct and opposite sides distinct, which is the classical statement.
   Tangent lines (A = B) are not covered in the projective form. That would need "side AB =
   tangent at A" when `A = B`. The vector identity itself says nothing useful there, since
   `A×A = 0`.
4. **Scope of "conic".** The result is stated for the zero set of any nonzero quadratic form. That
   includes line pairs (Pappus follows as a corollary, not yet stated) and double lines. Over
   non-closed fields a nonzero form can have an empty or one-point zero set; the theorem is then
   vacuous or trivial, which is fine.
5. **Generality.** `K` is a field (Stage 3) or an integral domain (Stage 2). The ambient space is
   concretely `Fin 3 → K`. A Mathlib version might want any 3-dimensional `V`; that can be
   transported via a basis.
6. **Style and performance.** The `ring` proofs of the two degree-12, 18-variable identities take
   80–95 s and about 2.6 GB each. The CI time is acceptable, but a Mathlib reviewer might object.
   One could reduce this by factoring the Veronese determinant through brackets (Plücker/Grassmann
   relations) or by normalising coordinates. I also used `simp` with `Fin.succAbove` to expand the
   6×6 determinant; a `det_fin_six`-free route might be preferred. Otherwise the proofs are short.
7. The main theorem should probably also be stated with `Collinear`-style hypotheses in the
   affine/Euclidean plane, which is how `docs/100.yaml` and the `plby` statement phrase it.
   The route is to embed ℝ² into ℙ² and transfer collinearity. That is more glue code.

## 4. Remaining-work estimate
- (1) projective conic predicate, plus a Pappus corollary: about 0.5 day.
- (2) `IsCollinear {mk u, mk v, mk w} ↔ u ⬝ᵥ v ⨯₃ w = 0`, plus a version with
  auxiliary-point hypotheses: 1–2 days.
- (7) affine/Euclidean-plane corollary matching the `100.yaml` style (circle or general conic in
  ℝ² with `Collinear ℝ`): 1–3 days. Most of that is glue for ℝ² → ℙ², including points at
  infinity when opposite sides are parallel.
- Mathlib PR polish (naming, docstrings, speeding up the 90 s `ring`s, generalising V): 2–4 days,
  plus review.

**Total:** about 1–2 weeks to a mergeable PR. The mathematical core is finished.

## 5. Prior formalisations found
Searched GitHub code (`gh search code "Pascal" "hexagon" --language=lean`, `pascal_hexagon`,
`pascal conic`) and repos, plus a web search for the Zulip archive. The web search found no
relevant Zulip thread. `mathlib4/docs/100.yaml` lists #28 with no declaration, and there is also
an entry in `docs/1000.yaml`.

- **`plby/lean-proofs`**, `src/latest/HundredTheorems/Theorem28.lean`, 866 lines, updated
  2026-09-15. States `theorem pascal_hexagon` for **six distinct points on a circle** in
  `EuclideanSpace ℝ (Fin 2)`, with `Collinear ℝ` hypotheses and conclusion. The file contains no
  `sorry` and ends with `#print axioms`. The header says it was "proven formally by Aristotle
  (Harmonic), given an informal proof by ChatGPT-5.2 Pro". The proof goes through complex numbers
  and the unit circle. **This is a genuine sorry-free Lean 4 proof, but only for circles.** The
  statement file is at `src/latest/ComparatorChallenges/HundredTheorems/Theorem28.lean`.
- **`rjwalters/lean-genius`**, `proofs/Proofs/PascalsHexagon.lean`, 1712 lines, updated
  2026-09-27. Projective, over ℝ, with a symmetric-matrix conic. The main
  `pascal_hexagon_theorem` uses `axiom conic_implies_pascal_constraint` (line 255). Axiom-free
  pieces: the standard conic, plus the symmetric non-degenerate case through Sylvester's law of
  inertia (`proof_sketch_conic_implies_pascal`). It notes that the degenerate case is still open.
  The word `sorry` appears only in docstrings, which claim the non-degenerate path is 0-sorry.
- **`facebookresearch/atlas-lean`**, `v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean`.
  Takes the Bézout/Cayley–Bacharach route with `[IsAlgClosed k]`. Bézout is left as `sorry`.
- `level0000x/Lv-00` mentions `pascal_theorem` only as a name in a list; there is no proof.

## 6. Numerical sanity check
`code/check_pascal.py` uses exact `Fraction` arithmetic with seed 2026. Each of 300 trials checks:
- a random conic through a rational point, with 6 rational points found by secant lines:
  `pascalDet = 0`;
- a perturbed control, which gives a nonzero value;
- the identity `pascalDet = −det(Veronese)` on random points;
- the parametric points `(s², st, t²)`;
- a line pair (the Pappus configuration).

Output: `OK: 300 trials (conic, Veronese identity, parametric, line-pair/Pappus)`.
I also checked both core identities symbolically with sympy (bracket form, and the Veronese
quotient = −1) before starting the Lean proofs.

## Files
```
PascalHexagon.lean                 imports all modules
PascalHexagon/Defs.lean            definitions
PascalHexagon/StandardConic.lean   Stage 1
PascalHexagon/Bracket.lean         pascalDet = bracket polynomial
PascalHexagon/Veronese.lean        det(Veronese) = −bracket polynomial
PascalHexagon/Conic.lean           Stage 2
PascalHexagon/Projective.lean      Stage 3
code/check_pascal.py               numerical check
```
Build with `lake build`. Build modules one at a time: the three `ring` modules each peak at about
2.6 GB. When I built `Bracket` together with the full `Mathlib` import (an earlier attempt), the
4 GB cgroup OOM-killer fired. Minimal imports avoid this.
