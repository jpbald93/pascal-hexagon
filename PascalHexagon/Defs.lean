import Mathlib.LinearAlgebra.CrossProduct

/-!
# Pascal's hexagon theorem: definitions

Points of the projective plane are represented by vectors in `K³ = Fin 3 → K`.
* The line through `u` and `v` is `u ⨯₃ v`; the intersection point of two lines `l, m` is
  `l ⨯₃ m`.
* Three points `u, v, w` are collinear iff the triple product `u ⬝ᵥ v ⨯₃ w`
  (`= det ![u, v, w]`, Mathlib's `triple_product_eq_det`) vanishes.

For a hexagon `A B C D E F` the three "Pascal points" are
`(A×B)×(D×E)`, `(B×C)×(E×F)`, `(C×D)×(F×A)`, and `pascalDet` is their triple product.
-/

open Matrix

namespace PascalHexagon

variable {K : Type*} [CommRing K]

/-- The bracket `[u v w]`, i.e. the determinant with rows `u, v, w`. -/
def br (u v w : Fin 3 → K) : K := u ⬝ᵥ v ⨯₃ w

/-- The bracket polynomial `[ABE][BCF][CDA][DEF] - ...` which equals the Pascal determinant. -/
def pascalBracket (A B C D E F : Fin 3 → K) : K :=
  br A B E * br B C F * br C D A * br D E F - br A B E * br B C F * br C D F * br D E A
    + br A B E * br B C E * br C D F * br D F A - br A B D * br B C E * br C D F * br E F A

/-- Triple product of the three Pascal points of the hexagon `A B C D E F`. -/
def pascalDet (A B C D E F : Fin 3 → K) : K :=
  ((A ⨯₃ B) ⨯₃ (D ⨯₃ E)) ⬝ᵥ ((B ⨯₃ C) ⨯₃ (E ⨯₃ F)) ⨯₃ ((C ⨯₃ D) ⨯₃ (F ⨯₃ A))

/-- The degree-2 Veronese map `(x, y, z) ↦ (x², y², z², xy, yz, zx)`. -/
def ver (v : Fin 3 → K) : Fin 6 → K :=
  ![v 0 ^ 2, v 1 ^ 2, v 2 ^ 2, v 0 * v 1, v 1 * v 2, v 2 * v 0]

/-- The 6×6 matrix whose rows are the Veronese images of six points. -/
def verMatrix (A B C D E F : Fin 3 → K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of ![ver A, ver B, ver C, ver D, ver E, ver F]

end PascalHexagon
