/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection

/-! # Unbounded proper mate projection step

This is the proper-factor identity used in the restricted coefficient projection.
It removes the bounded-below witnesses from the existing mate calculation; the
remaining open-factor calculation is handled by the parent theorem.
(blueprint: lem-pur-etale-quotient-tensor-projection-proper-mate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The unbounded scalar mate followed by direct-image restriction is the proper
projection map after the canonical scalar/tensor identification.
Source: Zheng, Proposition 2.29(2), Construction 2.26; Stacks Tag 0GL6.
(blueprint: lem-pur-etale-quotient-tensor-projection-proper-mate).

Proof: resolve an arbitrary derived object by a K-flat complex with flat terms.
The scalar/pullback normalization and the tensor comparison give the displayed
square on that representative. Naturality and localization extensionality pass it
to the unbounded derived category; the mate counit equation identifies the
result with the proper projection map.
-/
theorem scalarMate_restrict_eq_projection_unbounded
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (J : DerivedCategoryModule A Z) :
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ).map
        ((scalarMate φ f).app J) ≫
        (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ Z).obj J) =
      (scalarTensorIso φ W).hom.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj J) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) Z).obj J).map
              (scalarCoefficientPullbackIso φ f).hom ≫
            (scalarTensorIso φ Z).inv.app J) := by
  sorry

end AlgebraicGeometry.Etale
