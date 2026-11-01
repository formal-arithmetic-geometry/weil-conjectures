/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts

import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSourceChartScalarTransition

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

private theorem map_chart_scalar {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {A B : C} {E : D} (s t : A ≅ B) (c : F.obj B ≅ E) (r : ℕ)
    (h : s.inv ≫ t.hom = r • 𝟙 B) :
    (F.mapIso s ≪≫ c).inv ≫ (F.mapIso t ≪≫ c).hom = r • 𝟙 E := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Category.assoc]
  rw [← F.map_comp_assoc, h, Functor.map_nsmul, F.map_id]
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
    Iso.inv_hom_id]

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
  have : IsAlgClosed P.field.k := IsAlgClosure.isAlgClosed P.field.k₀
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
    have hscalar := P.exists_finiteReductionSourceChartScalar d ζ η hζ hη
    obtain ⟨r, hr⟩ := hscalar
    have hs : (s ζ hζ).inv ≫ (s η hη).hom = r • 𝟙 _ := by
      exact map_chart_scalar F
        (P.finiteReductionSourceTrivialization f d ζ hζ K)
        (P.finiteReductionSourceTrivialization f d η hη K) c r (hr f K)
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
end BaseChange

end WeilConjectures.PurityFiniteSetting
