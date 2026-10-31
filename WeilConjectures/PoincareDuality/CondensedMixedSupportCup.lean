/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.PoincareDuality.CondensedPointTensor
public import WeilConjectures.SixFunctors.CondensedAffineRestrictionLocality

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
/-- The native adjunction, with exact pullback in its canonically derived presentation.
Source: native module adjunction in the defining display
(blueprint: def-pod-mixed-support-cup-product). -/
def adjunction (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull Λ f ⊣ push Λ f :=
  (derivedUpperStarLowerStarAdjunction Λ.X f).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Proper projection, inverse open-support projection, inverse pullback compositor,
then the native module counit. This is the site-valued defining mixed-support map.
Source: both defining displays
(blueprint: def-pod-mixed-support-cup-product). -/
def site (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K L : Ambient Λ X) :
    (support Λ c).obj K ⊗ (push Λ f).obj L ⟶ (support Λ c).obj (K ⊗ L) :=
  supportProjection Λ c K ((push Λ f).obj L) ≫
    (support Λ c).map (𝟙 K ⊗ₘ (adjunction Λ f).counit.app L)

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
/-- The right-support convention is the signed swap on the point, the left cup, then
compact support of the signed site swap. No properness hypothesis is used.
Source: support-order display
(blueprint: def-pod-mixed-support-cup-product). -/
def rightCup (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} (c : Compactification f)
    (K L : Ambient Λ X) :
    (condensedRingOrdinaryCoefficientComplex Λ.X f).obj L ⊗
      (condensedRingCompactCoefficientComplex Λ.X c).obj K ⟶
        (condensedRingCompactCoefficientComplex Λ.X c).obj (L ⊗ K) :=
  letI : BraidedCategory (Ambient Λ X) := TraceCupPoint.siteBraiding Λ.X X
  letI : BraidedCategory (DerivedCategory (ModuleCat.{u + 1} (Γ Λ.X))) :=
    TraceCupPoint.scalarBraiding Λ.X
  (β_ ((condensedRingOrdinaryCoefficientComplex Λ.X f).obj L)
    ((condensedRingCompactCoefficientComplex Λ.X c).obj K)).hom ≫
      cup Λ k c K L ≫
        (condensedRingCompactCoefficientComplex Λ.X c).map (β_ K L).hom

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupMixed
