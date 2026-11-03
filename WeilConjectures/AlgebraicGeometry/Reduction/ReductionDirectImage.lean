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

/-- The canonical coefficient comparison is an isomorphism in the full subcategory
of bounded intrinsically constructible complexes of finite Tor amplitude. Membership
is written out for both endpoints, so no etale-origin hypothesis replaces intrinsic
constructibility. No flatness or finite-projective-dimension condition is imposed.
Source: blueprint main-20261015, sk-lem-sp-reduction-direct-image.md
(blueprint: det-sp-reduction-direct-image).

Proof:
1. Transfer the intrinsic bounded constructible finite-Tor predicate through the exact
   fixed-coefficient realization equivalence. Homology commutes with realization, finite
   support is equivalent to t-structure boundedness, and the Tor transport theorem
   identifies the two Tor tests. The supported etale tensor-origin theorem supplies
   bounded K = j_!L and H = K tensor B, together with the canonical comparison to j_!M.
2. The existing module-sheaf direct-image bound over a field supplies one bound 2d for
   every coefficient sheaf. The finite ring A is Noetherian and the finite A-module B
   is finitely presented. Apply the finite-constant projection component theorem to K
   and B. Its finite-free approximation argument uses a finite cohomological window,
   without requiring a finite projective resolution of B over A.
3. The normalized etale-origin scalar projection square identifies the restriction of
   the specified B-linear proper mate with this projection, conjugated by canonical
   tensor and direct-image isomorphisms. Cancel the source factors and reflect the
   resulting isomorphism through restriction. Naturality transports it to j_!M.
   Proper image of the specified open scalar isomorphism completes the comparison.
4. The existing compact-support preservation argument in fixed coefficients, transported
   through the compact realization isomorphism, gives intrinsic Dctf membership.
   Apply it over A, followed by scalar preservation on Y, for the source. Apply scalar
   preservation on X, followed by compact support over B, for the target.
5. The companion cocycle theorem applies a categorical pasting lemma to the existing
   proper and open cocycles. That lemma uses only functoriality, associativity and
   naturality of the second proper comparison at the first open comparison.
-/
theorem reductionDirectImage_isIso
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (M : proEtaleDerivedCategory X A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M))
    (hTor : HasFiniteProEtaleTorAmplitude X A M) :
    IsIso ((reductionDirectImageComparison φ j p).app M) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)) := by
  have hM : ReductionGood X A M := ⟨hbounded, hconstructible, hTor⟩
  have hRf := reductionGood_compactSupport ℓ pchar hℓ k f j p hf A hA M hM
  have hsource := reductionGood_scalar ℓ hA hB φ Y _ hRf
  have hMB := reductionGood_scalar ℓ hA hB φ X M hM
  have htarget := reductionGood_compactSupport ℓ pchar hℓ k f j p hf B hB _ hMB
  have hiso : IsIso ((reductionDirectImageComparison φ j p).app M) := by
    let E := sfIntrinsicDerivedEquivalence X A
    let K := E.inverse.obj M
    have hK := reductionGood_iso (E.counitIso.app M).symm hM
    have hctf := (reductionGood_realization_iff X A K).mp hK
    have hc := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
      _ hctf.1
    have torsion {R : Type u} [CommRing R]
        (h : ∃ n : ℕ, ∀ x : R, (ℓ ^ n) • x = 0) : ∃ n : ℕ, (ℓ : R) ^ n = 0 := by
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hn 1⟩
    have hcf (i : ℤ) : IsConstructibleProEtaleFixedModuleSheaf X (ULift.{u + 1} A)
        ((DerivedCategory.homologyFunctor _ i).obj K) := by
      exact (fixed_constructible_iff _ X _).mpr (hc.2 i)
    obtain ⟨L, hL, hLc, e, hJ, hH, hJplus, hHplus, hex⟩ :=
      SupportedEtaleTensorOrigin.supported_etale_tensor_origin ℓ (Fact.out : ℓ.Prime)
        φ (torsion hA) (torsion hB) j K hc.1 hcf hK.2.2
    let ei : (finiteCoefficientIntrinsicDerivedComparison Z A).obj
          ((SupportedEtaleTensorOrigin.etaleOpen A j).obj L) ≅
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory).obj M :=
      (FiniteCompactScalar.intrinsicSiteFunctorIso A Z).app _ ≪≫
      (sfIntrinsicDerivedEquivalence Z A).functor.mapIso
        (SupportedEtaleTensorOrigin.supportedComparison A j L K e) ≪≫
      (SupportedEtaleTensorOrigin.openPresentation A j).symm.app K ≪≫
      ((sfIntrinsicExtensionByZero j A).mapDerivedCategory).mapIso (E.counitIso.app M)
    have hi := reductionProper_isIso φ k p
      ((SupportedEtaleTensorOrigin.etaleOpen A j).obj L) hJ hH.1
    have : IsIso ((directImageScalarComparison φ p).app
        (((sfIntrinsicExtensionByZero j A).mapDerivedCategory).obj M)) :=
      (NatTrans.isIso_app_iff_of_iso (directImageScalarComparison φ p) ei).mp hi
    dsimp only [reductionDirectImageComparison, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact ⟨hiso, hsource.1, hsource.2.1, hsource.2.2,
    htarget.1, htarget.2.1, htarget.2.2⟩

set_option maxHeartbeats 18000 in
-- Diagnose elaboration without unfolding large derived-functor constructions indefinitely.
set_option maxHeartbeats 12000 in
-- Keep categorical transport elaboration within a predictable resource bound.
set_option maxHeartbeats 12000 in
-- Keep categorical transport elaboration within a predictable resource bound.
end AlgebraicGeometry.ProEtale
