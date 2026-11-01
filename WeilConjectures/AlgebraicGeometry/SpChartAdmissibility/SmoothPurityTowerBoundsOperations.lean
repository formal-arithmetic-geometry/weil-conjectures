/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerOperationsGroundFieldRetagging
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated

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

private theorem support_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : proEtaleCohomologicalSupport K ⊆ Set.Icc a b) :
    proEtaleCohomologicalSupport L ⊆ Set.Icc a b := by
  intro i hi
  apply h
  intro hz
  exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mp hz)

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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
