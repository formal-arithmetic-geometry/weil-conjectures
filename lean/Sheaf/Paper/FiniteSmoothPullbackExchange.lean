/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.FiniteReductionRootCharts

import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.FiniteSourceChartScalarTransition
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality

/-! # The specified smooth pullback exchange

Source: blueprint main-20261015, def-pur-smooth-pullback-exchange
(blueprint: def-pur-smooth-pullback-exchange).
The exchange is the literal purity composite with the canonical middle source map.

## Main definitions

- `finiteReductionBaseChangeSource`: the canonical tensor/pullback source map.
- `finiteReductionSmoothExchange`: inverse pulled-back purity, source map, purity.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.Scheme

/-- The exact realization pullback has its termwise shift comparison.
Source: blueprint base-change statement (blueprint: def-pur-smooth-pullback-exchange).
Proof: the ordinary inverse image is exact and additive, hence its termwise derived
functor commutes with cochain shift. Transport this comparison through the published
realization equivalences, using their termwise shift comparisons. -/
instance finiteReductionPullbackCommShift (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (P.finiteReductionPullback f).CommShift ℤ := by
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
  exact inferInstanceAs
    (((Scheme.sfIntrinsicModuleEquivalence Y P.Ring).inverse.mapDerivedCategory ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory ⋙
      (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor.mapDerivedCategory).CommShift ℤ)

/-- Pullback composition through the very same realization units as gamma.
Source: blueprint base-change statement, c_(h,g)
(blueprint: def-pur-smooth-pullback-exchange). -/
def finiteReductionPullbackCompositor (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :
    (P.finiteReductionPullback (f ≫ g)).obj K ≅
      (P.finiteReductionPullback f).obj ((P.finiteReductionPullback g).obj K) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso
    ((compositionFixedPullbackComp P.Ring f g).app
        ((Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K) ≪≫
      (P.smoothPurityPullback f).mapIso
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app
          ((P.smoothPurityPullback g).obj
            ((Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K))))

/-- The canonical inverse-image square from its two compositors and its commutativity.
Source: blueprint base-change statement, middle identification
(blueprint: def-pur-smooth-pullback-exchange). -/
def finiteReductionPullbackSquare (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReductionPullback u).obj ((P.finiteReductionPullback f).obj K) ≅
      (P.finiteReductionPullback f').obj ((P.finiteReductionPullback v).obj K) :=
  (P.finiteReductionPullbackCompositor u f K).symm ≪≫
    eqToIso (congrArg (fun h ↦ (P.finiteReductionPullback h).obj K) sq.w) ≪≫
    P.finiteReductionPullbackCompositor f' v K

private theorem scalar_chart_composite {C : Type*} [Category C] [Preadditive C]
    {A B D E : C} (s s' : A ≅ B) (t t' : D ≅ E) (m : B ≅ E) (r : ℕ)
    (hs : s.inv ≫ s'.hom = r • 𝟙 B) (ht : t.inv ≫ t'.hom = r • 𝟙 E) :
    s ≪≫ m ≪≫ t.symm = s' ≪≫ m ≪≫ t'.symm := by
  have hs' : s'.hom = r • s.hom := by
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      Preadditive.comp_nsmul, Category.comp_id] using
      congrArg (fun z ↦ s.hom ≫ z) hs
  apply Iso.ext
  apply (cancel_mono t'.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [ht]
  simp only [Preadditive.comp_nsmul, Category.comp_id, hs', Preadditive.nsmul_comp]

/-- The tensor/twist source identification for a square is uniquely fixed in root charts.
This is b_square, with ordinary pullback compositors, tensor pullback and root restriction.
Source: def-pur-smooth-pullback-exchange, middle identification
(blueprint: def-pur-smooth-pullback-exchange).
Proof: trivialize the root line on the base by a primitive root. Tensor pullback
and the termwise shift comparison identify both sides with the shifted double
pullback. The two pullback compositors and the square's equality give the middle
map. Changing the primitive root rescales both sides by the same unit to the same
power, so the composite is independent of that chart. A chart exists because the
base field is algebraically closed and ell differs from its characteristic; its
equation determines the isomorphism uniquely. -/
theorem existsUnique_finiteReductionBaseChangeSource (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    ∃! b : (P.finiteReductionPullback u).obj ((P.compositionShiftedPullback f d).obj K) ≅
      (P.compositionShiftedPullback f' d).obj ((P.finiteReductionPullback v).obj K),
      ∀ (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent),
        b = (P.finiteReductionPullback u).mapIso
            (P.finiteReductionSourceTrivialization f d ζ hζ K) ≪≫
          ((P.finiteReductionPullback u).commShiftIso (2 * (d : ℤ))).app _ ≪≫
          (shiftFunctor _ (2 * (d : ℤ))).mapIso
            (P.finiteReductionPullbackSquare u f' f v sq K) ≪≫
          (P.finiteReductionSourceTrivialization f' d ζ hζ
            ((P.finiteReductionPullback v).obj K)).symm := by
  classical
  have hunit : IsUnit (P.diagonalExponent : P.field.k) := by
    simpa only [map_natCast] using
      (P.diagonalExponent_isUnit (𝟙 (Spec (.of P.field.k)))).map
        (Scheme.ΓSpecIso (.of P.field.k)).hom.hom
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨hunit.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X'
  let F := P.finiteReductionPullback u
  have : F.Additive := inferInstanceAs
    (((Scheme.sfIntrinsicModuleEquivalence X P.Ring).inverse.mapDerivedCategory ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) u).mapDerivedCategory ⋙
      (Scheme.sfIntrinsicModuleEquivalence X' P.Ring).functor.mapDerivedCategory).Additive)
  let c := (F.commShiftIso (2 * (d : ℤ))).app ((P.finiteReductionPullback f).obj K)
  let m := (shiftFunctor _ (2 * (d : ℤ))).mapIso
    (P.finiteReductionPullbackSquare u f' f v sq K)
  let s (η : P.field.k) (hη : IsPrimitiveRoot η P.diagonalExponent) :=
    F.mapIso (P.finiteReductionSourceTrivialization f d η hη K) ≪≫ c
  let t (η : P.field.k) (hη : IsPrimitiveRoot η P.diagonalExponent) :=
    P.finiteReductionSourceTrivialization f' d η hη ((P.finiteReductionPullback v).obj K)
  refine ⟨s ζ hζ ≪≫ m ≪≫ (t ζ hζ).symm, ?_, ?_⟩
  · intro η hη
    obtain ⟨r, hr⟩ := P.exists_finiteReductionSourceChartScalar d ζ η hζ hη
    have hs : (s ζ hζ).inv ≫ (s η hη).hom = r • 𝟙 _ := by
      dsimp only [s]
      simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
        Category.assoc]
      rw [← F.map_comp_assoc, hr f K, Functor.map_nsmul, F.map_id]
      simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
        Iso.inv_hom_id]
    simpa only [s, t, m, c, Iso.trans_assoc] using
      scalar_chart_composite (s ζ hζ) (s η hη) (t ζ hζ) (t η hη) m r hs
      (hr f' ((P.finiteReductionPullback v).obj K))
  · intro b hb
    simpa only [s, t, m, c, Iso.trans_assoc] using hb ζ hζ

/-- The source identification of the actual purity-defined base-change square.
Source: def-pur-smooth-pullback-exchange
(blueprint: def-pur-smooth-pullback-exchange). -/
def finiteReductionBaseChangeSource (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReductionPullback u).obj ((P.compositionShiftedPullback f d).obj K) ≅
      (P.compositionShiftedPullback f' d).obj ((P.finiteReductionPullback v).obj K) :=
  (P.existsUnique_finiteReductionBaseChangeSource u f' f v sq d K).choose

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


section BaseChange
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X X' Y Y' : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
variable [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X' ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
variable (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
variable [u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
variable [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
variable (sq : IsPullback u f' f v) (d : ℕ)
variable [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']

set_option linter.unusedSectionVars false in
/-- Pullback of a finite-Tor constructible object has the required finite-Tor domain.
Source: def-pur-smooth-pullback-exchange, domains
(blueprint: def-pur-smooth-pullback-exchange).
Proof: inverse image is exact, preserves flat modules, and sends a bounded flat
model to a bounded flat model in the same Tor interval. Pull back the finite
constructible stratification and use the canonical finite-coefficient realization.
This proves the intrinsic finiteTorConstructible predicate without any flatness,
smoothness or properness requirement on the base morphism. -/
theorem finiteReductionBaseChangeInput (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y'
      ((P.finiteReductionPullback v).obj K) := by
  classical
  let A := P.Ring
  let B := P.Coefficient
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive A Y
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive A Y'
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y
  let E := Scheme.sfIntrinsicDerivedEquivalence Y A
  obtain ⟨hconstruct, a, b, ht⟩ := hK
  obtain ⟨c, hc⟩ := hconstruct.1.bddBelow
  obtain ⟨e, he⟩ := hconstruct.1.bddAbove
  have hvan : ∀ i : ℤ, (i < min c e ∨ e < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K) := by
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (hc hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (he hz)) hi
  obtain ⟨J, ⟨eJ⟩⟩ := ((Scheme.finiteRing_constructibleDerived_origin Y A).2.2.1 K).mpr
    ⟨hconstruct.2, min c e, e, min_le_right _ _, hvan⟩
  let ecomp := (Functor.mapDerivedCategoryCompIso ν
    (Scheme.sfIntrinsicModuleEquivalence Y A).functor).app J.obj
  let eK : ν.mapDerivedCategory.obj J.obj ≅ E.inverse.obj K :=
    E.functor.preimageIso (ecomp.symm ≪≫ eJ ≪≫ (E.counitIso.app K).symm)
  let J' := (Etale.upperStar (ModuleCat.{u + 1} B) v).mapDerivedCategory.obj J.obj
  have hbc := (etaleBounded_iff Y B J.obj).mp J.property
  have hbc' : Etale.DerivedCategory.isBoundedConstructible B Y' J' :=
    (etaleBounded_iff Y' B J').mpr (hbc.mapDerivedCategory_upperStar v)
  let ν' := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y'
  let E' := Scheme.sfIntrinsicDerivedEquivalence Y' A
  let square := (Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} B) v) ν').symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) v).symm ≪≫
    Functor.mapDerivedCategoryCompIso ν (ProEtale.upperStar (ModuleCat.{u + 1} B) v)
  let eJ' : (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y' A).obj J' ≅
      (P.finiteReductionPullback v).obj K :=
    (Functor.mapDerivedCategoryCompIso ν'
      (Scheme.sfIntrinsicModuleEquivalence Y' A).functor).app J' ≪≫
      E'.functor.mapIso ((square.app J.obj) ≪≫ (P.smoothPurityPullback v).mapIso eK)
  have hout := ((Scheme.finiteRing_constructibleDerived_origin Y' A).2.2.1
    ((P.finiteReductionPullback v).obj K)).mp ⟨⟨J', hbc'⟩, ⟨eJ'⟩⟩
  have comparison (T : Scheme.{u}) (L : Etale.DerivedCategoryModule B T)
      (hp : _root_.DerivedCategory.TStructure.t.plus L) :
      Etale.DerivedCategory.hasTorAmplitudeIn B T a b L ↔
        Scheme.HasProEtaleTorAmplitude T A
          ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).obj L) a b := by
    let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T
    let R := ProEtale.finiteCoefficientIntrinsicRealization T A
    let := Scheme.sfIntrinsicModuleEquivalence_functor_additive A T
    let : R.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive T A
    let : PreservesFiniteLimits R :=
      ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits T A
    let : PreservesFiniteColimits R :=
      ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits T A
    let e := (Functor.mapDerivedCategoryCompIso C R).app L
    exact (ProEtale.comparison_torAmplitudeIn_iff A T a b ht.1 ⟨L, hp⟩).trans
      ⟨fun h ↦ torAmplitude_of_iso T A e.symm a b h,
        fun h ↦ torAmplitude_of_iso T A e a b h⟩
  have htJ := (comparison Y J.obj hbc.1.1).mpr
    (torAmplitude_of_iso Y A eJ.symm a b ht)
  have htJ' : Etale.DerivedCategory.hasTorAmplitudeIn B Y' a b J' := by
    apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
    exact (Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) Y' a b).prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).app J.obj)
      (Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} B) v a b
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htJ))
  refine ⟨⟨?_, hout.1⟩, a, b, ?_⟩
  · obtain ⟨c', e', _, hv⟩ := hout.2
    apply (Set.finite_Icc c' e').subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hv i (.inl h))),
      le_of_not_gt (fun h ↦ hi (hv i (.inr h)))⟩
  · exact torAmplitude_of_iso Y' A eJ' a b
      ((comparison Y' J' ((etaleBounded_iff Y' B J').mp hbc').1.1).mp htJ')

/-- The canonical smooth purity morphism is invertible on its stated domain.
Source: def-pur-smooth-purity-map, tau / Pi / theta
(blueprint: def-pur-smooth-pullback-exchange).
Proof: tau is the specified tensor-shift isomorphism, Pi is the specified diagonal
purity isomorphism, and theta is invertible by thm-pur-cohomological-smoothness.
Tensoring the inverse of Pi preserves its inverse equations. Their composite,
transported through the realization equivalence, is therefore an isomorphism. -/
theorem finiteReductionPurityIsIso (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    IsIso (P.smoothPurityMap f d K hK) := by
  classical
  -- Retain the original intrinsic K and obtain only coordinates for its etale origin.
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  have hc := (Scheme.finiteRing_constructibleDerived_origin Y P.Ring).2.2.1 K
  have hOrigin : (ObjectProperty.ι
      (Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison Y P.Ring).essImage K := by
    apply hc.mpr
    refine ⟨hK.1.2, ?_⟩
    obtain ⟨a, ha⟩ := hK.1.1.bddBelow
    obtain ⟨b, hb⟩ := hK.1.1.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge ((min_le_left a b).trans (ha hn))) hi
    · exact (not_lt_of_ge ((hb hn).trans (le_max_right a b))) hi
  obtain ⟨J, ⟨eJ⟩⟩ := hOrigin
  let : (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).functor.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring).Additive
  let ecomp := (Functor.mapDerivedCategoryCompIso ν
    (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).functor).app J.obj
  let e : ν.mapDerivedCategory.obj J.obj ≅ E.inverse.obj K :=
    E.functor.preimageIso (ecomp.symm ≪≫ eJ ≪≫ (E.counitIso.app K).symm)
  have hplus : _root_.DerivedCategory.TStructure.t.plus J.obj := by
    obtain ⟨a, b, _, hz⟩ := J.property.2
    exact ⟨a, (_root_.DerivedCategory.isGE_iff J.obj a).mpr
      (fun i hi ↦ hz i (.inl hi))⟩
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  let : HasCompactification f := inferInstance
  let : HasInvertibleExponent P.Coefficient X :=
    P.finiteComparedInvertibleExponent (X ↘ Spec (.of P.field.k))
  -- The existing orientation-free theorem supplies exactly the canonical tensor mate.
  obtain ⟨_, _, _, _, htheta⟩ :=
    Etale.exists_dualizingComplex_iso_and_tensor P.Coefficient f d
  have : IsIso (Etale.dualizingComplexTensorMap P.Coefficient f J.obj) := htheta J.obj
  have : IsIso (smoothPurityEtaleTheta P.Coefficient f J.obj) := by
    unfold smoothPurityEtaleTheta
    infer_instance
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y J.obj hplus
  have : IsIso (P.smoothPurityTheta f (E.inverse.obj K) J.obj e) := by
    unfold smoothPurityTheta
    infer_instance
  have : IsIso (P.smoothPurityTensorMapInPresentation f d
      (Y ↘ Spec (.of P.field.k)) (E.inverse.obj K) J.obj e) := by
    unfold smoothPurityTensorMapInPresentation
    infer_instance
  -- The defining uniqueness theorem fixes the map itself in these coordinates.
  have hmap := (P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose_spec J.obj e
  have : IsIso (P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose := by
    rw [hmap]
    infer_instance
  unfold smoothPurityMap smoothPurityTensorMap
  infer_instance


/-- The actual smooth exchange is the literal purity composite, not a separately
chosen right-adjoint base-change mate. Its middle arrow was fixed above independently.
Source: def-pur-smooth-pullback-exchange, displayed composite
(blueprint: def-pur-smooth-pullback-exchange). -/
def finiteReductionSmoothExchange (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (P.finiteReductionPullback u).obj ((P.compositionExceptional f).obj K) ≅
      (P.compositionExceptional f').obj ((P.finiteReductionPullback v).obj K) := by
  letI := P.finiteReductionPurityIsIso f d K hK
  letI := P.finiteReductionPurityIsIso f' d ((P.finiteReductionPullback v).obj K)
    (P.finiteReductionBaseChangeInput v K hK)
  exact ((P.finiteReductionPullback u).mapIso (asIso (P.smoothPurityMap f d K hK))).symm ≪≫
    P.finiteReductionBaseChangeSource u f' f v sq d K ≪≫
    asIso (P.smoothPurityMap f' d ((P.finiteReductionPullback v).obj K)
      (P.finiteReductionBaseChangeInput v K hK))

end BaseChange

end WeilConjectures.PurityFiniteSetting
