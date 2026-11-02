/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensor
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AffineRestrictionLocality.CondensedAffineRestrictionLocality

/-! # Mixed-support cup in native condensed modules

Source: latest blueprint, def-pod-mixed-support-cup-product. The proper/open
projection word and native pullback counit are used before exact point evaluation.
(blueprint: def-pod-mixed-support-cup-product)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupMixed

open AffineRestrictionLocality

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Proper projection, inverse open-support projection, inverse pullback compositor,
then the native module counit. This is the site-valued defining mixed-support map.
Source: both defining displays
(blueprint: def-pod-mixed-support-cup-product). -/
def site (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K L : Ambient Λ X) :
    (support Λ c).obj K ⊗ (push Λ f).obj L ⟶ (support Λ c).obj (K ⊗ L) :=
  exceptionalProjectionMorphismOfCompactification Λ.X c K ((push Λ f).obj L) ≫
    (support Λ c).map
      (𝟙 K ⊗ₘ (derivedUpperStarLowerStarAdjunction Λ.X f).counit.app L)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The specified coefficient-complex mixed-support cup: inverse point tensor comparison,
followed by point evaluation of the site-valued map. Its scalar ring is Λ(*).
Source: the definition of mu_c
(blueprint: def-pod-mixed-support-cup-product). -/
@[irreducible] def cup (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} (c : Compactification f)
    (K L : Ambient Λ X) :
    (condensedRingCompactCoefficientComplex Λ.X c).obj K ⊗
      (condensedRingOrdinaryCoefficientComplex Λ.X f).obj L ⟶
        (condensedRingCompactCoefficientComplex Λ.X c).obj (K ⊗ L) :=
  TraceCupPoint.tensor Λ.X k _ _ ≫ (TraceCupPoint.fiber Λ.X k).map (site Λ c K L)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupMixed
