/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement

/-! # Exact computation maps in native inverse-image balance

Source: Stacks Tags 03D7 and 06YY; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-native-pullback-exact-counits)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

/-- Exact scalar extension has an invertible computation map on every complex.
Source: Stacks Tag 06YY.
(blueprint: lem-sf-native-pullback-exact-counits).

Proof: its exact termwise functor inverts all quasi-isomorphisms after localization.
The universal left-derived counit is therefore invertible. The cochain computation
map only conjugates this counit by quotient factorization isomorphisms. This also
covers unbounded complexes and zero rings. -/
theorem nativePullbackScalarCounit_isIso {X : Scheme.{u}}
    {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (c : A ⟶ B)
    [PreservesFiniteLimits (pbcExtend c)] [PreservesFiniteColimits (pbcExtend c)]
    (P : CochainComplex (pbcModules X A) ℤ) : IsIso (pbcComplexCounit c P) := by
  let W := HomotopyCategory.quasiIso (pbcModules X A) (.up ℤ)
  have h : W.IsInvertedBy ((pbcExtend c).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh) := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W (pbcExtend c).mapDerivedCategoryFactorsh]
    exact MorphismProperty.IsInvertedBy.of_comp W DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh W) (pbcExtend c).mapDerivedCategory
  let := pbcDerivedExtension_universal c
  let : IsIso (pbcExtensionCounit c) :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts (pbcDerivedExtend c)
      (pbcExtensionCounit c) h
  unfold pbcComplexCounit
  infer_instance

/-- Ordinary integral pullback is exact before completing its output.
Source: Stacks Tag 03D7 and Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-sf-native-pullback-exact-counits).

Proof: the completed integral coefficient inverse-image map is an isomorphism.
The associated ringed module inverse image is exact. Its right adjoint is ordinary
integral direct image: both coefficient maps have the same finite quotient projections.
Uniqueness of left adjoints identifies the two ordinary inverse images and transports
finite-limit preservation. Colimits are preserved by the integral adjunction. -/
theorem nativePullbackIntegralExact (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    PreservesFiniteLimits (ordinaryIntegralModulePull l E p) ∧
      PreservesFiniteColimits (ordinaryIntegralModulePull l E p) := by
  let A := PurCompactSupport.completed l E
  have hm : proEtaleRingDirectImageMap p (A.ring Y) (A.ring X) (A.pull p) =
      sfCompletedCoefficientMap l E p :=
    (proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E p)
  let e : proEtaleRingModuleDirectImage p (A.ring Y) (A.ring X) (A.pull p) ≅
      ordinaryIntegralModulePush l E p := by
    unfold proEtaleRingModuleDirectImage ordinaryIntegralModulePush
    rw [hm]
    exact SheafOfModules.pushforwardCongr (IntegralOrdinary.directRing_eq l E p)
  let b := ((proEtaleRingModuleAdjunction p (A.ring Y) (A.ring X)
    (A.pull p)).ofNatIsoRight e).leftAdjointUniq (ordinaryIntegralModuleAdjunction l E p)
  have : PreservesFiniteLimits (ordinaryIntegralModulePull l E p) :=
    preservesFiniteLimits_of_natIso b
  have : PreservesColimitsOfSize.{0, 0} (ordinaryIntegralModulePull l E p) :=
    (ordinaryIntegralModuleAdjunction l E p).leftAdjoint_preservesColimits
  exact ⟨inferInstance, inferInstance⟩

/-- The actual integral computation counit is invertible on all cochain inputs.
Source: Stacks Tag 06YY; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-native-pullback-exact-counits).

Proof: ordinary integral pullback is exact, so its termwise functor inverts all
quasi-isomorphisms. The universal derived counit is consequently an isomorphism.
The published cochain counit differs only by its quotient factorization isomorphisms;
hence it too is an isomorphism, without boundedness or K-flat hypotheses. -/
theorem nativePullbackIntegralCounit_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    IsIso (ordinaryIntegralPullComplexCounit l E p P) := by
  have := (nativePullbackIntegralExact l E p).1
  have := (nativePullbackIntegralExact l E p).2
  let F := ordinaryIntegralModulePull l E p
  let W := HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)
  have h : W.IsInvertedBy (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W F.mapDerivedCategoryFactorsh]
    exact MorphismProperty.IsInvertedBy.of_comp W DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh W) F.mapDerivedCategory
  let : (ordinaryIntegralDerivedPull l E p).IsLeftDerivedFunctor
      (ordinaryIntegralPullCounit l E p) W := by
    unfold ordinaryIntegralDerivedPull ordinaryIntegralPullCounit
    infer_instance
  let : IsIso (ordinaryIntegralPullCounit l E p) :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts (ordinaryIntegralDerivedPull l E p)
      (ordinaryIntegralPullCounit l E p) h
  unfold ordinaryIntegralPullComplexCounit
  infer_instance

/-- A normalized native inverse-image counit is invertible for an invertible
coefficient map. Source: Stacks Tag 06YY; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-native-pullback-exact-counits).

Proof: restriction along an invertible coefficient map is an equivalence. Its
scalar-extension left adjoint is an equivalence as well and is therefore exact.
The scalar computation counit is invertible on every complex by exactness.
Normalization expresses the given counit as this map conjugated by the exact
inverse-image and identity-cancellation isomorphisms. All three factors are invertible. -/
theorem nativePullbackNormalizedCounit_isIso {X Y : Scheme.{u}} (p : X ⟶ Y)
    {A : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage p).obj A ⟶ B) [IsIso c]
    [(ContinuousRational.modulePull p c).Additive]
    (δ : DerivedCategory.Q ⋙ ContinuousRational.derivedPull p c ⟶
      (ContinuousRational.modulePull p c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hδ : ContinuousRational.IsNormalizedPullCounit p c δ)
    (P : CochainComplex (pbcModules Y A) ℤ) : IsIso (δ.app P) := by
  let : (pbcRestrict c).IsEquivalence :=
    inferInstanceAs (ProEtale.CondensedRing.ringModuleEquivalenceOfIso X
      ((adicLisseForget X).mapIso (asIso c))).functor.IsEquivalence
  let : (pbcExtend c).IsEquivalence :=
    (pbcScalarAdjunction c).isEquivalence_left_of_isEquivalence_right
  obtain ⟨e, eC, heC, he, h⟩ := hδ
  rw [h]
  have := nativePullbackScalarCounit_isIso c
    (((proEtaleRingModulePullback p A ((adicTowerInverseImage p).obj A)
      (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P)
  infer_instance

end WeilConjectures.AdicQbarRealization.Proper
