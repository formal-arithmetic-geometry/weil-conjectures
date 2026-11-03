/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationTotalCounit.VectorIntegrationTotalCounitMaps
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationTotalCounitCoordinates
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationTotalCounitExchange
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceLinearTraceInvariance

/-! # Simultaneous sum-chart trace transported to the flattened double tower

This comparison stops before the two-block adjunction normalization.
(blueprint: lem-pur-vector-integration-total-counit-geometric).
-/

@[expose] public noncomputable section
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem four_assoc {C : Type*} [Category C] {W X Y Z R : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ R) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem finish_trace {C : Type*} [Category C] {X Y Z T R : C}
    (f : X ⟶ Y) (a : Y ⟶ Z) (e : Z ⟶ T) (b : T ⟶ T) (d : X ⟶ T)
    (q : Z ⟶ R) (q' : T ⟶ R) (hp : f ≫ a ≫ e ≫ b = d)
    (he : e ≫ q' = q) (hi : b ≫ q' = q') : f ≫ a ≫ q = d ≫ q' := by
  rw [← hp]
  simp only [Category.assoc, hi, he]

attribute [local irreducible] rightDerivedLowerShriek upperStar lowerStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme
  leftDerivedUpperStarComp leftDerivedUpperStarIsoMapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

end AlgebraicGeometry.Etale
