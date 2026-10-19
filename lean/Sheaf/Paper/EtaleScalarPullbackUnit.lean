/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection

/-! # Scalar-adjunction unit for the canonical etale pullback comparison

Source: Stacks Project, Tags 07A4 and 07A7.
(blueprint: lem-r2-etale-scalar-pullback-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The specified pullback comparison intertwines the scalar-adjunction units.
Source: Stacks Tags 07A4 and 07A7
(blueprint: lem-r2-etale-scalar-pullback-unit).
Proof: compute on a flat-term K-flat representative P. The scalar representative
map is the adjunct of the ordinary scalar unit, by its definition. The geometric
representative is the derived counit followed by the homotopy quotient comparison.
Apply the normalization equation defining scalarPullbackIso, transpose through the
scalar adjunction on X, and use the factorization of the exact geometric adjunction
unit. This gives the ordinary scalar/pullback square, whose comparison is the
conjugate under the composite adjunctions. Its unit identity is the ordinary
adjunction triangle identity. The invertible resolving counits cancel, giving the
displayed equality at Q(P). Every object has such a representative. Naturality of
the two sides transports the equality along its isomorphism to an arbitrary K.
No properness, boundedness or flatness of the coefficient homomorphism is used. -/
theorem scalarPullbackUnit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A Y) :
    L(upperStar (ModuleCat.{u + 1} A) f).map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).unit.app K) ≫
      (scalarRestrictionPullbackIso φ f).hom.app ((scalarExtension φ Y).obj K) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
          ((scalarPullbackIso φ f).hom.app K) =
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app
          (L(upperStar (ModuleCat.{u + 1} A) f).obj K) := by
  sorry

end AlgebraicGeometry.Etale
