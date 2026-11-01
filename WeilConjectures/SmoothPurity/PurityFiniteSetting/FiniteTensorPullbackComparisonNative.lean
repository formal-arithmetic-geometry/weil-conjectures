/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # The recorded finite pullback comparison is the native scalar mate

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2; Stacks Project, Tag 07A4.
(blueprint: lem-pur-finite-tensor-pullback-comparison-native)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

attribute [local implicit_reducible] WeilConjectures.PurityFiniteSetting.Coefficient
  Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
  Scheme.sfIntrinsicDerivedEquivalence WeilConjectures.PurityFiniteSetting.coefficientCommRing
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor ProEtale.upperStar ProEtale.sheafExtendScalars
  Functor.leftDerivedFunctorCounit Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  HasDerivedCategory.standard

namespace WeilConjectures.PurityFiniteSetting

/-- The recorded fixed-scalar pullback comparison `finiteTensorPullbackComparison` is the
native pro-étale scalar/pullback mate `scalarPullbackProEtaleIso`, read through the
identifications of the derived pullbacks with `mapDerivedCategory`.
Source: thm-pur-finite-reduction-of-purity, proof Step 2; Stacks 07A4
(blueprint: lem-pur-finite-tensor-pullback-comparison-native).
Proof: `finiteTensorPullbackComparison` is the preimage under the realization equivalence
of the composite of the inverse scalar presentation on `X`, the pullback model, the
recorded intrinsic pullback comparison, the scalar presentation on `Y` and the reduced
pullback model. By faithfulness of the realization it suffices to compare the realized
maps. The intrinsic pullback normalization identifies the recorded intrinsic comparison
with the inverse ordinary scalar mate; the étale-origin restriction and extension cubes
and the scalar presentation compatibility carry the étale scalar presentations to the
pro-étale coefficient extension; the factorized representative of the scalar pullback
comparison and the recorded open normalization identify the result with the inverse of
the pro-étale scalar mate, conjugated by `leftDerivedUpperStarIsoMapDerivedCategory`.
The realization units and counits cancel by the triangle identities. -/
theorem finiteTensorPullbackComparison_native (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteTensorPullbackComparison m hm hmn f K).hom =
      (P.finiteTensorReduction m hm hmn X).map
          ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) f).inv.app K) ≫
        (ProEtale.scalarPullbackProEtaleIso
          (P.finiteReductionRingHom m hm hmn).ulift f).inv.app K ≫
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) f).hom.app
          ((P.finiteTensorReduction m hm hmn Y).obj K) := by
  sorry

end WeilConjectures.PurityFiniteSetting
