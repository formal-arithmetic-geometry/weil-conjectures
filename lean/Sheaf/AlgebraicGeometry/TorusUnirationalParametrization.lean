module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Unirational parametrizations of tori over arbitrary fields

Source: Milne, Algebraic Groups (2017), Definition 12.59 and Propositions 12.60,
12.63, 12.64, printed pp.250--251
(blueprint: lem-sfb-torus-unirational-parametrization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every torus over any field admits a dominant morphism from a nonempty open
subscheme of a finite-dimensional affine space over that field.
Source: Milne, Algebraic Groups (2017), Definition 12.59 and Proposition 12.64,
printed pp.250--251 (blueprint: lem-sfb-torus-unirational-parametrization).

Proof:
1. Apply lem-sfb-torus-induced-quotient to obtain finite separable extensions L_i/k,
   with a nonempty finite index set, and a torus P representing the units of
   A tensor R for A = product L_i. There is a homomorphism P -> T surjective on
   scheme points. A redundant factor L_i = k permits the same construction for
   the trivial torus.
2. Concatenate bases of the L_i to obtain a finite k-basis of A, of size d >= 1.
   By lem-sfb-finite-algebra-units-affine-chart, the determinant of multiplication
   defines a principal open U in affine d-space and an isomorphism U -> P over k.
   The coordinates of 1_A have determinant 1, so U is nonempty. Over a general
   test algebra the determinant must be a unit, which gives the unit functor.
3. Compose U -> P with P -> T. This is a k-morphism surjective on scheme points:
   lift a point of T to P and then along the inverse of the isomorphism U -> P.
   Consequently every nonempty open of T has nonempty inverse image. Its image
   is dense, as asserted. No perfection or infinitude of k is used. -/
theorem torus_unirational_parametrization {k : Type u} [Field k]
    (T : Grp (Over (Spec (.of k)))) (hT : MultiplicativeType.IsTorus T) :
    ∃ (n : ℕ) (U : (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))).Opens),
      Nonempty U.toScheme ∧ ∃ q : U.toScheme ⟶ T.X.left,
        q ≫ T.X.hom = U.ι ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘
          Spec (.of k)) ∧ IsDominant q := by
  sorry

end AlgebraicGeometry
