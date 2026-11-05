/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Constant-coefficient pro-etale pullback comparison

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
pur713-def-pullback-comparison.md (blueprint: pur713-def-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

-- Reuse the adjunction calculation from ProfiniteCoefficientInverseImage.

namespace AlgebraicGeometry.Scheme

/--
The canonical derived comparison for two composable morphisms with constant
coefficients, in the direction from the iterated pullback to the pullback of
the composite.
Source: the composition clause of
literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
pur713-def-pullback-comparison.md (blueprint: pur713-def-pullback-comparison).
-/
@[no_expose] noncomputable def proEtaleConstantRingPullbackComposition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A k ⋙
        proEtaleConstantRingDerivedPullback A h ≅
      proEtaleConstantRingDerivedPullback A (h ≫ k) :=
  (proEtaleCanonicalPullbackComposition h k
    (proEtaleConstantRing V A) (proEtaleConstantRing W A)
    (proEtaleConstantRing Z A)
    (proEtaleConstantRingComparison k A)
    (proEtaleConstantRingComparison h A)).symm ≪≫
    eqToIso (congrArg (fun c ↦
      proEtaleRingDerivedPullback (h ≫ k)
        (proEtaleConstantRing V A) (proEtaleConstantRing Z A) c)
      (proEtaleConstantRingCompositeCoefficients_eq h k A))

end AlgebraicGeometry.Scheme

end
