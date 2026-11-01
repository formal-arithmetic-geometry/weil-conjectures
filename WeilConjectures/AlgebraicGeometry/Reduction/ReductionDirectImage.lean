/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.Compactification.NagataCompactification

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero

import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantProjectionFormula
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageScalarCocycle
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarCocycle
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginScalarProjectionSquare
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport

/-!
# Compact support and finite coefficient extension

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.md (blueprint: det-sp-reduction-direct-image).

The comparison uses the specified counit mate and the unit-normalized open tensor
comparison. All categories are ordinary uncompleted module derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
-- Replaying categorical transport tactics for linting duplicates elaboration work.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  completedAdicDerivedChange directImageScalarComparison reductionOpenScalarIso
  scalarExtensionFunctor_composition
  Etale.derivedTensor Etale.lowerStar Etale.upperStar
  Etale.rightDerivedLowerStarProjectionMap Etale.scalarTensorIso

private def ReductionGood (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory T A) : Prop :=
  Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj K)} ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
    HasFiniteProEtaleTorAmplitude T A K

private theorem reductionGood_iso {T : Scheme.{u}} {A : Type u} [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (h : ReductionGood T A K) :
    ReductionGood T A L := by
  refine ⟨h.1.subset (fun i hi hz ↦ hi
    (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)),
    fun i ↦ intrinsicConstructible_of_iso T A
      ((DerivedCategory.homologyFunctor _ i).mapIso e) (h.2.1 i), ?_⟩
  obtain ⟨a, b, ht⟩ := h.2.2
  refine ⟨a, b, ht.1, ?_⟩
  intro N P hN f hf hP M i hi
  obtain ⟨q⟩ := hN
  exact ht.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

private theorem bounded_iff_finite_support
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    DerivedCategory.TStructure.t.bounded K ↔
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi ((DerivedCategory.isGE_iff K a).mp ha i h)),
      le_of_not_gt (fun h ↦ hi ((DerivedCategory.isLE_iff K b).mp hb i h))⟩
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨⟨a, (DerivedCategory.isGE_iff K a).mpr (fun i hi ↦ ?_)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).mpr (fun i hi ↦ ?_)⟩⟩
    · by_contra hz
      exact (not_lt_of_ge (ha hz)) hi
    · by_contra hz
      exact (not_lt_of_ge (hb hz)) hi

private theorem reductionGood_realization_iff (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (K : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    ReductionGood T A ((sfIntrinsicDerivedEquivalence T A).functor.obj K) ↔
      ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T K := by
  let F := (sfIntrinsicModuleEquivalence T A).functor
  have hc (i : ℤ) :
      IsConstructibleProEtaleModuleSheaf T A
        ((DerivedCategory.homologyFunctor _ i).obj (F.mapDerivedCategory.obj K)) ↔
      IsConstructible (ULift.{u + 1, u} A)
        ((DerivedCategory.homologyFunctor _ i).obj K) := by
    let e := (F.mapDerivedCategoryHomologyFunctorIso i).app K
    constructor
    · intro h
      exact (intrinsicRealization_constructible_iff T A _).mp
        (intrinsicConstructible_of_iso T A e.symm h)
    · intro h
      exact intrinsicConstructible_of_iso T A e
        ((intrinsicRealization_constructible_iff T A _).mpr h)
  constructor
  · rintro ⟨hb, hconstructible, a, b, ht⟩
    have hbk : DerivedCategory.TStructure.t.bounded K :=
      F.bounded_of_bounded_mapDerivedCategory_obj ((bounded_iff_finite_support _).mpr hb)
    have hbc := ProEtale.DerivedCategory.boundedConstructible_of_homology
      (ULift.{u + 1, u} A) hbk (fun i ↦
        exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _ ((hc i).mp (hconstructible i)))
    exact ⟨hbc, a, b, (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A T a b ht.1 K).mp ht⟩
  · intro h
    have hbci := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
      _ h.1
    refine ⟨(bounded_iff_finite_support _).mp
      (F.bounded_mapDerivedCategory_obj hbci.1), fun i ↦ (hc i).mpr (hbci.2 i), ?_⟩
    obtain ⟨a, b, ht⟩ := h.2
    refine ⟨min a b, max a b, ?_⟩
    exact (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A T (min a b) (max a b) (min_le_max) K).mpr
        (DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) (le_max_right _ _) ht)

private theorem reductionGood_compactSupport
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [IsProper p] (hf : j ≫ p = f)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (M : proEtaleDerivedCategory X A) (hM : ReductionGood X A M) :
    ReductionGood Y A ((reductionCompactSupport A j p).obj M) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k)) := by
    obtain ⟨n, hn⟩ := hA
    have hz : ((ℓ ^ n : ℕ) : ULift.{u + 1} A) = 0 := by
      apply ULift.ext
      change ((ℓ ^ n : ℕ) : A) = 0
      simpa only [nsmul_eq_mul, mul_one] using hn 1
    have hne : (ℓ : k) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓ
    have hu : IsUnit ((ℓ ^ n : ℕ) : k) := by
      rw [Nat.cast_pow]
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hne)
    exact ⟨ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos _, hz, by
      simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  have : HasInvertibleExponent (ULift.{u + 1} A) Y :=
    HasInvertibleExponent.of_hom (Y ↘ Spec (.of k))
  let c : Compactification f := ⟨Z, p, j, hf.symm, inferInstance, inferInstance⟩
  have : HasCompactification f := c.hasCompactification
  let E := sfIntrinsicDerivedEquivalence X A
  let K := E.inverse.obj M
  have hK := reductionGood_iso (E.counitIso.app M).symm hM
  obtain ⟨hF, R, ha⟩ := CondensedRing.ordinary_small_adjunction A k
    (Y ↘ Spec (.of k)) f c
  have ho := hF K ((reductionGood_realization_iff X A K).mp hK)
  have ht := (reductionGood_realization_iff Y A _).mpr ho
  let er := (FiniteCompactScalar.compactRealizationIso A c).app K
  let ep := (Functor.isoWhiskerLeft
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory (properOriginPushIso A p)).app M
  exact reductionGood_iso
    (er.symm ≪≫ (sfIntrinsicCompactSupport c A).mapIso (E.counitIso.app M) ≪≫ ep.symm) ht

set_option maxHeartbeats 18000 in
-- Diagnose elaboration without unfolding large derived-functor constructions indefinitely.
private theorem scalarMateRestriction_reflectsIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u}) :
    (scalarMateRestriction φ Y).mapDerivedCategory.ReflectsIsomorphisms := by
  let r := scalarMateRestriction φ Y
  have : PreservesFiniteLimits r :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).1
  have : PreservesFiniteColimits r :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).2.1
  have : r.ReflectsIsomorphisms :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).2.2
  refine ⟨fun f _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (r.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff (r.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ r

set_option maxHeartbeats 18000 in
-- Diagnose elaboration without unfolding large derived-functor constructions indefinitely.
set_option maxHeartbeats 12000 in
-- Keep categorical transport elaboration within a predictable resource bound.
set_option maxHeartbeats 12000 in
-- Keep categorical transport elaboration within a predictable resource bound.
end AlgebraicGeometry.ProEtale
