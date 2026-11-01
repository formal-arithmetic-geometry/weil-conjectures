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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
