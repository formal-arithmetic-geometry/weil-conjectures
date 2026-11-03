/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOriginRecursiveData

/-! # Comparison of the supported coordinate cup with the tensor Cartier recursion

Source: `det-sp-trace-basic`, Proof (2), cup products and the proper projection formula
(blueprint: lem-sp-affine-origin-cup-recursion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The explicit zero-locus cup is the iterated coefficient-first tensor Cartier arrow.

Source: `det-sp-trace-basic`, Proof (2), coordinate product calculation
(blueprint: lem-sp-affine-origin-cup-recursion).

Proof: induct on the number of coordinates. For zero coordinates the empty-locus
isomorphism, finite base change for the identity square, and the unit of identity
pullback identify the empty class with the identity direct-image comparison.
For the successor, `(finRange (d+1)).reverse` starts with the last coordinate, followed
by `finRange d` in the old coordinates. Its divisor is the last zero section. The
remaining equations are the pullbacks of the old coordinate equations. Finite base
change identifies their intersection support with the composite of the two zero
sections. Apply naturality of the ordinary supported Kummer boundary to identify the
last supported class with the pullback of the coordinate-line class; uniqueness of
the invertible boundary identifies the chosen representatives. The definition of
supported cup, followed by the multiplication isomorphism of closed constant sheaves,
is the coefficient-first proper projection map with the previous class, followed by
tensoring with the last supported class. Cancel its inverse closed projection map.
This gives the successor of `affineOriginRecursiveClass`. The canonical Tate product
and pullback comparisons commute with this equation: this is tensor associativity,
the shift-addition coherence, and naturality of the Kummer power comparison. The
chosen normalized Tate transport agrees with the projective-line one by uniqueness.
Finally, finite base change along the fixed affine-space/tower isomorphism and
naturality of derived direct-image composition give precisely the stated equality.
All classes have even shift, so permuting tensor factors introduces no sign. The
empty base and the zero coefficient ring use the same functorial equations.
-/
theorem affineOriginCanonicalClass_eq_recursive
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineOriginCanonicalClass A N hN hA S hS d =
      affineOriginRecursiveClass A N hN hA S hS d := by
  sorry

end AlgebraicGeometry.Etale
