/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompactificationExact
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtaleDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! # Exact étale sum calculus on coefficient towers

The étale calculus is constructed independently of any compactification compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

private theorem tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) {a c : ℤ}
    (h : HasProEtaleTorAmplitude T A K a c) : HasProEtaleTorAmplitude T A L a c := by
  refine ⟨h.1, ?_⟩
  intro C P he f hf hP M i hi
  exact h.2 C P (he.map (fun z ↦ z ≪≫ e.symm)) f hf hP M i hi

private theorem sum_preservesFlat (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [WeaklyEtale e] :
    (weaklyEtaleLowerShriek (ModuleCat.{u + 1} A) e).PreservesFlat := by
  let L := weaklyEtaleLowerShriek (ModuleCat.{u + 1} A) e
  let G := upperStar (ModuleCat.{u + 1} A) e
  let adj := weaklyEtaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e
  have hp (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :
      IsIso (Functor.Monoidal.projectionMap adj M) := by
    have := isIso_ihomComparison_upperStar (ModuleCat.{u + 1} A) e M
    exact Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison adj M
  refine ⟨fun {N} hN ↦ ?_⟩
  have := hN.tensorRight.preservesFiniteLimits
  have := hN.tensorRight.preservesFiniteColimits
  let τ : G ⋙ MonoidalCategory.tensorRight N ⋙ L ≅
      MonoidalCategory.tensorRight (L.obj N) :=
    NatIso.ofComponents (fun M ↦ by
      have := hp M
      exact asIso ((Functor.Monoidal.projectionMap adj M).app N))
      (by
        intro M M' f
        dsimp only [Functor.comp_map]
        exact Functor.Monoidal.projectionMap_naturality_left adj f N)
  have hr : exactFunctor _ _ (MonoidalCategory.tensorRight (L.obj N)) :=
    (exactFunctor_iff _).2
      ⟨preservesFiniteLimits_of_natIso τ, preservesFiniteColimits_of_natIso τ⟩
  have := hr.preservesFiniteLimits
  have := hr.preservesFiniteColimits
  exact ⟨(exactFunctor_iff _).2
    ⟨preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (L.obj N)).symm,
      preservesFiniteColimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (L.obj N)).symm⟩, hr⟩

private theorem transported_tor (A : Type u) [CommRing A] [Finite A]
    {U T : Scheme.{u}}
    (G : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1} A)) ⥤
      Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.PreservesFlat]
    (H : proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory T A)
    (τ : (sfIntrinsicDerivedEquivalence U A).functor ⋙ H ≅
      G.mapDerivedCategory ⋙ (sfIntrinsicDerivedEquivalence T A).functor)
    (K : proEtaleDerivedCategory U A) {a c : ℤ}
    (hK : HasProEtaleTorAmplitude U A K a c) :
    HasProEtaleTorAmplitude T A (H.obj K) a c := by
  let E := sfIntrinsicDerivedEquivalence U A
  let P := E.inverse.obj K
  have hP := (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A U a c hK.1 P).mp
    (tor_iso U A (E.counitIso.app K).symm hK)
  have hG := DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj G hP
  have hT := (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A T a c hK.1
    (G.mapDerivedCategory.obj P)).mpr hG
  exact tor_iso T A
    ((τ.app P).symm ≪≫ H.mapIso (E.counitIso.app K)) hT

private def transportDerivedIso (A : Type u) [CommRing A] [Finite A]
    {U T : Scheme.{u}}
    (G : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1} A)) ⥤
      Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (sfIntrinsicDerivedEquivalence U A).functor ⋙
        ((sfIntrinsicModuleEquivalence U A).inverse ⋙ G ⋙
          (sfIntrinsicModuleEquivalence T A).functor).mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ (sfIntrinsicDerivedEquivalence T A).functor :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence U A).funInvIdAssoc
        (G ⋙ (sfIntrinsicModuleEquivalence T A).functor)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private def comparisonSumIso (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙
        weaklyEtaleLowerShriek (ModuleCat.{u + 1} A) e ≅
      Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) T := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e))
    (ModuleCat.{u + 1} A) (ProEt.topology U) (ProEt.topology T)
  exact (((comparisonAdjunction (ModuleCat.{u + 1} A) U).comp adj).ofNatIsoRight
    (show _ ≅ comparisonLowerStar (ModuleCat.{u + 1} A) T ⋙
      Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance from
        Iso.refl _)).leftAdjointUniq
      ((Etale.etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
        (comparisonAdjunction (ModuleCat.{u + 1} A) T))

private def intrinsicComparisonSumIso (A : Type u) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    finiteCoefficientIntrinsicComparison U A ⋙ finiteEtaleExtension e A ≅
      Etale.etaleLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) e inferInstance ⋙
        finiteCoefficientIntrinsicComparison T A :=
  Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U)
    ((sfIntrinsicModuleEquivalence U A).funInvIdAssoc
      (weaklyEtaleLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) e ⋙
        (sfIntrinsicModuleEquivalence T A).functor)) ≪≫
    Functor.isoWhiskerRight (comparisonSumIso (ULift.{u + 1} A) e)
      (sfIntrinsicModuleEquivalence T A).functor

private theorem etaleBounded_iff (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hab i (.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hab i (.inr hi))⟩⟩, ?_⟩
    intro i
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨?_, min a b, b, min_le_right _ _, ?_⟩
    · intro i
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i)
    · intro i hi
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff K b).1 hb i hi

private noncomputable def intrinsicComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ProEtale.finiteCoefficientIntrinsicComparison Y A ⋙ proEtaleConstantRingPullback A f ≅
      Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A :=
  Functor.isoWhiskerLeft _ (openSquarePullbackModel A f) ≪≫
    (Functor.isoWhiskerLeft
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y)
      ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
          ProEtale.finiteCoefficientIntrinsicRealization X A))) ≪≫
    Functor.isoWhiskerRight
      (ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
      (ProEtale.finiteCoefficientIntrinsicRealization X A)

private noncomputable def intrinsicDerivedComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A ⋙
        proEtaleConstantRingDerivedPullback A f ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison X A :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (intrinsicComparisonPullbackIso f A) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

private theorem comparison_tor_iff (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (a b : ℤ) (hab : a ≤ b)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T)
    (hK : DerivedCategory.TStructure.t.plus K) :
    Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T a b K ↔
      HasProEtaleTorAmplitude T A
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).obj K) a b := by
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let R := ProEtale.finiteCoefficientIntrinsicRealization T A
  let e := (Functor.mapDerivedCategoryCompIso C R).app K
  have h := ProEtale.comparison_torAmplitudeIn_iff A T a b hab ⟨K, hK⟩
  exact h.trans ⟨fun h ↦ tor_iso T A e.symm h,
    fun h ↦ tor_iso T A e h⟩

private theorem constructible_transport (A : Type u) [CommRing A] [Finite A]
    {U T : Scheme.{u}}
    (H : proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory T A)
    (J : Etale.DerivedCategoryModule (ULift.{u + 1} A) U ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1} A) T)
    (τ : finiteCoefficientIntrinsicDerivedComparison U A ⋙ H ≅
      J ⋙ finiteCoefficientIntrinsicDerivedComparison T A)
    (hJ : ∀ P, Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) U P →
      Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T (J.obj P))
    (hH : ∀ K a c, HasProEtaleTorAmplitude U A K a c →
      HasProEtaleTorAmplitude T A (H.obj K) a c)
    (K : proEtaleDerivedCategory U A) (hK : spFiniteConstructibleTor U A K) :
    spFiniteConstructibleTor T A (H.obj K) := by
  obtain ⟨a, c, ht⟩ := hK.2.2
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin U A).2.2.1 K).mpr
    ⟨hK.2.1, hK.1⟩
  have hbc := (etaleBounded_iff U (ULift.{u + 1} A) L.obj).mp L.property
  have htL := (comparison_tor_iff U A a c ht.1 L.obj hbc.1.1).mpr
    (tor_iso U A eL.symm ht)
  have hct : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) U L.obj :=
    ⟨hbc, a, c, Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htL⟩
  let eP := (τ.app L.obj).symm ≪≫ H.mapIso eL
  have himage := ((finiteRing_constructibleDerived_origin T A).2.2.1 (H.obj K)).mp
    ⟨⟨J.obj L.obj, hJ L.obj hct⟩, ⟨eP⟩⟩
  exact ⟨himage.2, himage.1, a, c, hH K a c ht⟩


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite constructibility and unchanged Tor intervals for etale
sum extension and inverse image. The interval assertion applies to all unbounded inputs.
Source: Stacks 03DI, 03DJ, 03S5; latest blueprint Local pairs and Levels.

Proof: For Tor bounds take a K-flat representative P.
The ringed slice extension theorem makes e_!P K-flat and identifies its tensor
with H with e_!(P tensor e^*H); a module sheaf H therefore tests precisely the same
Tor interval. Pullback of a K-flat representative is K-flat. For a module sheaf G
on U, the projection formula identifies e_!(e^*K tensor G) with K tensor e_!G.
The latter has the specified interval. Exact extension reflects vanishing, as follows
from its structural-lift summand after restriction, so the former has that interval
before applying e_!. This uses every module-sheaf test, without constructibility.
For constructibility, choose bounded constructible etale origins at a finite level.
The graph-normalized comparison identifies sum extension with finite compact
support on such origins, and the finite compact-support-domain theorem supplies
constructibility and finite Tor amplitude. Etale chart pullback gives the inverse
image assertion. Transfer through the intrinsic module equivalences. These arguments
apply to any d because its underlying finite derived functor is the exact localization
of the fixed finiteEtaleExtension; its stored proof instances do not change that functor.
(blueprint: lem-v5-etale-finite-bounds). -/
theorem etale_finite_bounds
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    {U T : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [T.Over (Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (e : U ⟶ T) [e.IsOver (Spec (.of k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    (d : EtaleOperation l E b o z e) :
    (∀ n : ℕ,
      (∀ K : proEtaleDerivedCategory U (SpTowerShriek.R l E n),
      spFiniteConstructibleTor U (SpTowerShriek.R l E n) K →
      spFiniteConstructibleTor T (SpTowerShriek.R l E n)
        ((finiteEtaleDerived l E b o z d n).obj K)) ∧
    (∀ K : proEtaleDerivedCategory T (SpTowerShriek.R l E n),
      spFiniteConstructibleTor T (SpTowerShriek.R l E n) K →
      spFiniteConstructibleTor U (SpTowerShriek.R l E n)
        ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e).obj K))) ∧
    (∀ (n : ℕ) (a c : ℤ),
      (∀ K : proEtaleDerivedCategory U (SpTowerShriek.R l E n),
        HasProEtaleTorAmplitude U (SpTowerShriek.R l E n) K a c →
        HasProEtaleTorAmplitude T (SpTowerShriek.R l E n)
          ((finiteEtaleDerived l E b o z d n).obj K) a c) ∧
      (∀ K : proEtaleDerivedCategory T (SpTowerShriek.R l E n),
        HasProEtaleTorAmplitude T (SpTowerShriek.R l E n) K a c →
        HasProEtaleTorAmplitude U (SpTowerShriek.R l E n)
          ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e).obj K) a c)) := by
  classical
  have _ := hp
  let _ := q
  have : IsNoetherian U := isNoetherian_of_locallyOfFiniteType (U ↘ Spec (.of k))
  have : IsNoetherian T := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (.of k))
  have := hasCompactification_of_finiteType_over_field k U T e
  let compact := HasCompactification.compactification e
  suffices h : ∀ n : ℕ,
      ((∀ K, spFiniteConstructibleTor U (SpTowerShriek.R l E n) K →
        spFiniteConstructibleTor T (SpTowerShriek.R l E n)
          ((finiteEtaleDerived l E b o z d n).obj K)) ∧
       (∀ K, spFiniteConstructibleTor T (SpTowerShriek.R l E n) K →
        spFiniteConstructibleTor U (SpTowerShriek.R l E n)
          ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e).obj K))) ∧
      ∀ a c : ℤ,
       (∀ K, HasProEtaleTorAmplitude U (SpTowerShriek.R l E n) K a c →
        HasProEtaleTorAmplitude T (SpTowerShriek.R l E n)
          ((finiteEtaleDerived l E b o z d n).obj K) a c) ∧
       (∀ K, HasProEtaleTorAmplitude T (SpTowerShriek.R l E n) K a c →
        HasProEtaleTorAmplitude U (SpTowerShriek.R l E n)
          ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e).obj K) a c) from
    ⟨fun n ↦ (h n).1, fun n a c ↦ (h n).2 a c⟩
  intro n
  let A := SpTowerShriek.R l E n
  let B := ULift.{u + 1} A
  let G := weaklyEtaleLowerShriek (ModuleCat.{u + 1} B) e
  let H := finiteEtaleDerived l E b o z d n
  let F := proEtaleConstantRingDerivedPullback A e
  let := d.finiteAdditive n
  let := d.finiteLimits n
  let := d.finiteColimits n
  let : G.PreservesFlat := sum_preservesFlat B e
  have hsTor (K : proEtaleDerivedCategory U A) (a c : ℤ)
      (hK : HasProEtaleTorAmplitude U A K a c) :
      HasProEtaleTorAmplitude T A (H.obj K) a c :=
    transported_tor A G H (transportDerivedIso A G) K hK
  let τpull : (sfIntrinsicDerivedEquivalence T A).functor ⋙ F ≅
      (upperStar (ModuleCat.{u + 1} B) e).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence U A).functor :=
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryNatIso (openSquarePullbackModel A e)) ≪≫
      transportDerivedIso A (upperStar (ModuleCat.{u + 1} B) e)
  have hpTor (K : proEtaleDerivedCategory T A) (a c : ℤ)
      (hK : HasProEtaleTorAmplitude T A K a c) :
      HasProEtaleTorAmplitude U A (F.obj K) a c :=
    transported_tor A (upperStar (ModuleCat.{u + 1} B) e) F τpull K hK
  let τsum : finiteCoefficientIntrinsicDerivedComparison U A ⋙ H ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory ⋙
        finiteCoefficientIntrinsicDerivedComparison T A :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (intrinsicComparisonSumIso A e) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  have htors : ((l ^ (n + 1) : ℕ) : A) = 0 := by
    have hz := (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (I := spEllIdeal l E)
        (Ideal.subset_span (Set.mem_singleton (l : Padic.coefficientExtensionIntegers l E)))
        (n + 1)))
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hz
  have hℓk : (l : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : l.Prime) hne
  have : HasInvertibleExponent B (Spec (.of k)) :=
    ⟨l ^ (n + 1), pow_pos (Fact.out : l.Prime).pos _, by
      apply ULift.ext
      exact htors,
      by
        simpa using (isUnit_iff_ne_zero.mpr (pow_ne_zero (n + 1) hℓk)).map
          (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  have : HasInvertibleExponent B T := .of_hom (T ↘ Spec (.of k))
  refine ⟨⟨?_, ?_⟩, fun a c ↦ ⟨fun K hK ↦ hsTor K a c hK,
    fun K hK ↦ hpTor K a c hK⟩⟩
  · apply constructible_transport A H _ τsum
    · intro P hP
      have hc := (Etale.rightDerivedLowerShriekOfCompactification_isTriangulated_and_ctf
        B (k := k) compact).2.2 (T ↘ Spec (.of k)) hP
      exact (etaleBounded_iff T B _).mpr
        ((Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} B) T).prop_of_iso
          ((Etale.canonicalEtaleCompactSupportComparison B e compact).app P) hc.1)
    · exact hsTor
  · apply constructible_transport A F _ (intrinsicDerivedComparisonPullbackIso e A)
    · intro P hP
      exact (etaleBounded_iff U B _).mpr (hP.1.mapDerivedCategory_upperStar e)
    · exact hpTor

end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
