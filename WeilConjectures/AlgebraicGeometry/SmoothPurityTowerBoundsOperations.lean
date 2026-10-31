/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteLineTensorConditions
import WeilConjectures.AlgebraicGeometry.SignedLineTensorEquivalence
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization
import all WeilConjectures.AlgebraicGeometry.TowerOperationsGroundFieldRetagging
import all WeilConjectures.AlgebraicGeometry.FiniteCtfTriangulated

/-! # Separate uniform intervals under elementary tower operations

Source: blueprint latest, Local pairs and Uniformity
(blueprint: lem-route-elementary-tower-bounds).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpChartAdmissibility

private theorem torAmplitude_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) :
    HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

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
  exact h.trans ⟨fun h ↦ torAmplitude_of_iso T A e.symm a b h,
    fun h ↦ torAmplitude_of_iso T A e a b h⟩

/-- Pullback of an arbitrary finite constant coefficient ring preserves bounded
constructibility and the specified Tor interval. In particular it applies directly
to ell-power quotients, without changing the coefficient presentation.

Source: blueprint latest, sec-proetale-coefficients/sk-cor-pe-finite-tor-comparison/
lem-sf-pullback-tor-amplitude.proof.md; Stacks Tags 03D2, 0735 and 08FZ.
(blueprint: lem-sf-pullback-tor-amplitude).

Proof: descend the bounded constructible pro-etale complex through the finite-ring
intrinsic derived comparison. Exact etale inverse image preserves bounded
constructibility. The constant-ring comparison square identifies its realization
with the specified derived constant-ring pullback. Reflect the given Tor interval
through the comparison, pull a flat model back termwise, and reflect the same
interval back on X. Transport both conclusions along the comparison isomorphism.
The input finite-Tor witness is not used: the specified interval supplies one.
-/
private theorem finite_constant_pullback_bounds
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (A : Type u) [CommRing A] [Finite A] (f : X ⟶ Y)
    (K : proEtaleDerivedCategory Y A) (hK : spFiniteConstructibleTor Y A K)
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude Y A K a b) :
    spFiniteConstructibleTor X A ((proEtaleConstantRingDerivedPullback A f).obj K) ∧
      HasProEtaleTorAmplitude X A ((proEtaleConstantRingDerivedPullback A f).obj K)
        a b := by
  classical
  let B := ULift.{u + 1, u} A
  let F := proEtaleConstantRingDerivedPullback A f
  obtain ⟨c, d, hcd, hvan⟩ := hK.1
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin Y A).2.2.1 K).mpr
    ⟨hK.2.1, c, d, hcd, hvan⟩
  have hbc := (etaleBounded_iff Y B L.obj).mp L.property
  let P := (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj L.obj
  have hbcP : Etale.DerivedCategory.isBoundedConstructible B X P :=
    (etaleBounded_iff X B P).mpr (hbc.mapDerivedCategory_upperStar f)
  have hplus : DerivedCategory.TStructure.t.plus L.obj := hbc.1.1
  have hplusP : DerivedCategory.TStructure.t.plus P :=
    ((etaleBounded_iff X B P).mp hbcP).1.1
  have htL : Etale.DerivedCategory.hasTorAmplitudeIn B Y a b L.obj :=
    (comparison_tor_iff Y A a b hTor.1 L.obj hplus).mpr
      (torAmplitude_of_iso Y A eL.symm a b hTor)
  have htP : Etale.DerivedCategory.hasTorAmplitudeIn B X a b P := by
    apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
    exact (Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) X a b).prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} B) f).app L.obj)
      (Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} B) f a b
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htL))
  let eP : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj P ≅
      F.obj K :=
    ((intrinsicDerivedComparisonPullbackIso f A).app L.obj).symm ≪≫ F.mapIso eL
  have himage := ((finiteRing_constructibleDerived_origin X A).2.2.1 (F.obj K)).mp
    ⟨⟨P, hbcP⟩, ⟨eP⟩⟩
  have ht : HasProEtaleTorAmplitude X A (F.obj K) a b :=
    torAmplitude_of_iso X A eP a b
      ((comparison_tor_iff X A a b hTor.1 P hplusP).mp htP)
  exact ⟨⟨himage.2, himage.1, a, b, ht⟩, ht⟩


private theorem support_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : proEtaleCohomologicalSupport K ⊆ Set.Icc a b) :
    proEtaleCohomologicalSupport L ⊆ Set.Icc a b := by
  intro i hi
  apply h
  intro hz
  exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mp hz)

private theorem finite_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, s, t, ht⟩ := h
  refine ⟨⟨a, b, hab, ?_⟩, ?_, s, t, torAmplitude_of_iso T A e s t ht⟩
  · intro i hi
    exact (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro i
    have hcons := hc i
    rw [proEtaleModuleRestriction_constructible_iff] at hcons ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hcons

private theorem support_shift (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory T A) (a b j : ℤ)
    (h : proEtaleCohomologicalSupport K ⊆ Set.Icc a b) :
    proEtaleCohomologicalSupport (K⟦j⟧) ⊆ Set.Icc (a - j) (b - j) := by
  intro i hi
  have hi' : i + j ∈ proEtaleCohomologicalSupport K := by
    intro hz
    apply hi
    exact (((DerivedCategory.homologyFunctor _ 0).shiftIso j i (i + j)
      (add_comm j i)).app K).isZero_iff.mpr hz
  obtain ⟨ha, hb⟩ := h hi'
  exact ⟨by omega, by omega⟩

private theorem tor_shift (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory T A) (a b j : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) :
    HasProEtaleTorAmplitude T A (K⟦j⟧) (a - j) (b - j) := by
  refine ⟨by have hab := h.1; omega, ?_⟩
  intro L P hL f hf hP M i hi
  obtain ⟨F, c, htri, hcomp⟩ := Scheme.tensor_functor T A M
  obtain ⟨e⟩ := hL
  obtain ⟨q⟩ := hcomp L P f hf hP
  have hz := Scheme.tensor_homology_vanishes T A K a b M F hcomp h (j + i) (by omega)
  let hs := ((DerivedCategory.homologyFunctor _ 0).shiftIso j i (j + i) rfl).app (F.obj K)
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    (q.symm ≪≫ F.mapIso e ≪≫ (F.commShiftIso j).app K) ≪≫ hs)

private theorem finite_shift (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory T A) (j : ℤ) (h : spFiniteConstructibleTor T A K) :
    spFiniteConstructibleTor T A (K⟦j⟧) := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, s, t, ht⟩ := h
  refine ⟨⟨a - j, b - j, by omega, ?_⟩, ?_, s - j, t - j, tor_shift T A K s t j ht⟩
  · intro i hi
    have hz := hv (i + j) (by omega)
    exact (((DerivedCategory.homologyFunctor _ 0).shiftIso j i (i + j)
      (add_comm j i)).app K).isZero_iff.mpr hz
  · intro i
    have hi := hc (i + j)
    rw [proEtaleModuleRestriction_constructible_iff] at hi ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        (((DerivedCategory.homologyFunctor _ 0).shiftIso j i (i + j)
          (add_comm j i)).app K)).symm hi


private theorem finite_tensor_line_iso (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (S : SemilinearSections.Closed.{u + 1, u, u + 1} (ProEt.topology T)
      (proEtaleConstantRing T A))
    (models : SemilinearSections.Models.{u + 1, u, u + 1} (ProEt.topology T)
      (proEtaleConstantRing T A) S)
    (L : proEtaleRingModules T (proEtaleConstantRing T A))
    (hL : SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := proEtaleConstantRing T A) L)
    [(SheafOfModules.siteSheafTensorRight (A := proEtaleConstantRing T A) L).Additive]
    [PreservesFiniteLimits
      (SheafOfModules.siteSheafTensorRight (A := proEtaleConstantRing T A) L)]
    [PreservesFiniteColimits
      (SheafOfModules.siteSheafTensorRight (A := proEtaleConstantRing T A) L)]
    (K : proEtaleDerivedCategory T A) :
    Nonempty (S.tensor.obj (K, (DerivedCategory.singleFunctor _ 0).obj L) ≅
      (Functor.mapDerivedCategory
        (SheafOfModules.siteSheafTensorRight (A := proEtaleConstantRing T A) L)).obj K) := by
  classical
  let R := proEtaleConstantRing T A
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let G := DerivedCategory.Q.objPreimage K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (R := R) G
  have := hf
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨hSingle, _, hLim, hCol, _⟩ :=
    SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization R L hL
  have := hLim
  have := hCol
  let F := MonoidalCategory.tensorRight L
  let collapse := SheafOfModules.FlatSingleDerivedNormalization.collapse R L
  exact ⟨(S.tensor.mapIso (Iso.prod e
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app L).symm)).symm ≪≫
    (models.iso (ProEt.topology T) R S P
      ((CochainComplex.singleFunctor _ 0).obj L) hP hSingle).symm ≪≫
    DerivedCategory.Q.mapIso (collapse.app P) ≪≫
    (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫
    (Functor.mapDerivedCategoryNatIso (SheafOfModules.siteSheafTensorRightIso R L)).symm.app K⟩


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Inverse image and tensor with any specified strict Tate tower preserve both
intervals; a cochain shift subtracts its index from all four endpoints.
Source: blueprint latest, Local pairs and Uniformity, chart-admissibility steps 4--6
(blueprint: lem-route-elementary-tower-bounds).

Proof: everything is checked at a fixed level n, with finite coefficient ring
A = O_E/l^(n+1). For the first clause, geometry.pullEvaluation identifies the level of
the pulled tower with the constant-ring derived pullback of C_n. Descend C_n to a bounded
constructible etale origin (finiteRing_constructibleDerived_origin), reflect its Tor
interval to the etale side (comparison_torAmplitudeIn_iff), pull back by the exact etale
inverse image, which preserves bounded constructibility and the Tor interval
(torAmplitudeIn_leftDerivedUpperStar), and transport back through the intrinsic
comparison/pullback square built from openSquarePullbackModel. The exact inverse image
commutes with homology, so the cohomological interval [a,b] is kept separately.
For the second, l is a unit in k since l differs from p, hence in every residue field;
ellTwist_rank, signedLineTensor_equivalence and coefficientTwistLine_exact show that the
specified finite line R_n(r) is locally free of rank one with exact tensor, including
r = 0. On a K-flat representative of C_n the prescribed levelTensorModels and
flat_single_derived_normalization identify C_n tensor R_n(r)[0] with the derived exact
line-tensor functor, which preserves constructible homology and [s,t]
(finiteLineTensor_conditions) and, being exact, [a,b]. tensorEvaluation and w.level
identify this with the level of twist base w C r. The third clause uses evaluation's
shift comparison, H^i(C[j]) = H^(i+j)(C), and the same identity after tensoring a
degree-zero test module (finite_ctf_isTriangulated helpers) for the shifted Tor interval.
-/
theorem elementary_tower_bounds
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (hlp : l ≠ p)
    (base : SpTowerShriek.Base l E) (ops : SpTowerShriek.Operations l E base) :
    (∀ (X Y : Over (Spec (.of k))) [IsNoetherian X.left] [IsNoetherian Y.left]
      (f : X ⟶ Y) (C : SpTowerShriek.D l E Y.left) (a b s t : ℤ),
      bounds l E Y.left C a b s t →
      bounds l E X.left ((SpTowerShriek.pull l E base (ops.geometry f.left)).obj C)
        a b s t) ∧
    (∀ (T : Over (Spec (.of k))) [IsNoetherian T.left] (w : Twists l E T.left)
      (C : SpTowerShriek.D l E T.left) (r : ℕ) (a b s t : ℤ),
      bounds l E T.left C a b s t →
      bounds l E T.left (twist l E base w C r) a b s t) ∧
    (∀ (T : Scheme.{u}) (C : SpTowerShriek.D l E T) (j a b s t : ℤ),
      bounds l E T C a b s t →
      bounds l E T (C⟦j⟧) (a - j) (b - j) (s - j) (t - j)) := by
  let := base
  refine ⟨?_, ?_, ?_⟩
  · intro X Y _ _ f C a b s t hC n
    let A := SpTowerShriek.R l E n
    let F := proEtaleConstantRingPullback A f.left
    let e := ((ops.geometry f.left).pullEvaluation n).app C
    obtain ⟨hc, ht⟩ := finite_constant_pullback_bounds A f.left _ (hC n).1 s t (hC n).2.2
    refine ⟨finite_of_iso X.left A e.symm hc, ?_,
      torAmplitude_of_iso X.left A e.symm s t ht⟩
    apply support_of_iso X.left A e.symm a b
    intro i hi
    apply (hC n).2.1
    intro hz
    exact hi (((F.mapDerivedCategoryHomologyFunctorIso i).app
      ((SpTowerShriek.Ev l E Y.left n).obj C)).isZero_iff.mp (F.map_isZero hz))
  · intro T _ w C r a b s t hC n
    classical
    have hunit : IsUnit (l : k) := by
      apply (CharP.isUnit_natCast_iff (R := k) (Fact.out : p.Prime)).2
      intro h
      exact hlp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
        (Fact.out : l.Prime)).1 h).symm
    let residueMap (x : T.left) : k →+* T.left.residueField x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ T.hom.appTop ≫ T.left.Γevaluation x).hom
    let : ∀ x : T.left, Invertible (l : T.left.residueField x) := fun x ↦
      (map_natCast (residueMap x) l) ▸ (hunit.map (residueMap x)).invertible
    let A := SpTowerShriek.R l E n
    let R := SpTowerShriek.B l E T.left n
    let L := spEllTwistLine l E T.left n (r : ℤ)
    let M := (SpTowerShriek.Ev l E T.left n).obj C
    let F := SheafOfModules.siteSheafTensorRight (A := R) L
    let := ellTwist_rank l E T.left n
    let hRank := (signedLineTensor_equivalence T.left R
      (spEllTwistOne l E T.left n) (r : ℤ)).1
    let hExact := coefficientTwistLine_exact T.left (spEllTwistOne l E T.left n) (r : ℤ)
    have : L.IsFiniteLocallyFreeOfRank 1 := hRank
    have : F.Additive := hExact.1
    have : PreservesFiniteLimits F := hExact.2.1
    have : PreservesFiniteColimits F := hExact.2.2
    have hflat : SheafOfModules.IsFlatOnSite (J := ProEt.topology T.left) (R := R) L :=
      ⟨hExact.2.1, hExact.2.2⟩
    obtain ⟨eLine⟩ := finite_tensor_line_iso T.left A
      ((base.calculus T.left).levelClosed n)
      ((base.calculus T.left).levelTensorModels n) L hflat M
    let eSingle : (SpTowerShriek.Ev l E T.left n).obj
        ((DerivedCategory.singleFunctor _ 0).obj (w.tower r)) ≅
        (DerivedCategory.singleFunctor _ 0).obj L :=
      ((SpTowerShriek.ev l E T.left n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (w.level n r)
    let e : (SpTowerShriek.Ev l E T.left n).obj (twist l E base w C r) ≅
        F.mapDerivedCategory.obj M :=
      ((base.calculus T.left).tensorEvaluation n).app _ ≪≫
        ((base.calculus T.left).levelClosed n).tensor.mapIso
          (Iso.prod (Iso.refl M) eSingle) ≪≫ eLine
    have hc := finiteLineTensor_conditions T.left A L
    have ht := hc.2.2 M s t (hC n).2.2
    have hsupp : proEtaleCohomologicalSupport (F.mapDerivedCategory.obj M) ⊆
        proEtaleCohomologicalSupport M := by
      intro i hi hz
      exact hi (((F.mapDerivedCategoryHomologyFunctorIso i).app M).isZero_iff.mp
        (F.map_isZero hz))
    have hfinite : spFiniteConstructibleTor T.left A (F.mapDerivedCategory.obj M) := by
      obtain ⟨⟨c, d, hcd, hv⟩, hcons, _, _, _⟩ := (hC n).1
      refine ⟨⟨c, d, hcd, ?_⟩, ?_, s, t, ht⟩
      · intro i hi
        exact ((F.mapDerivedCategoryHomologyFunctorIso i).app M).isZero_iff.mp
          (F.map_isZero (hv i hi))
      · intro i
        have hci := hc.2.1 _ (hcons i)
        rw [proEtaleModuleRestriction_constructible_iff] at hci ⊢
        exact ProEtale.isConstructible_of_iso
          ((proEtaleModuleRestriction T.left A).mapIso
            ((F.mapDerivedCategoryHomologyFunctorIso i).app M)) hci
    exact ⟨finite_of_iso T.left A e.symm hfinite,
      support_of_iso T.left A e.symm a b (hsupp.trans (hC n).2.1),
      torAmplitude_of_iso T.left A e.symm s t ht⟩
  · intro T C j a b s t hC n
    let e := ((SpTowerShriek.Ev l E T n).commShiftIso j).app C
    exact ⟨finite_of_iso T _ e.symm (finite_shift T _ _ j (hC n).1),
      support_of_iso T _ e.symm _ _ (support_shift T _ _ a b j (hC n).2.1),
      torAmplitude_of_iso T _ e.symm _ _ (tor_shift T _ _ s t j (hC n).2.2)⟩

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
