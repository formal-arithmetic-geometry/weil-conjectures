/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.PurityCompositionCoherence
public import Sheaf.Paper.SmoothTrace
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

/-! # Reduction of the canonical finite-coefficient purity maps

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
def-pur-finite-reduction-chart-calculus (blueprint: def-pur-finite-reduction-chart-calculus).

## Main definitions

- `finiteReductionOrderedPower`: ordered tensor recursion.
- `finiteReductionComparisonUnitChart`: the exact-derived coefficient-unit chart.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
-- Publish the existing canonical Mathlib sheaf tensor instance so that these
-- native derived-unit normalizations also elaborate in importing modules.
attribute [instance] Sheaf.monoidalCategory
namespace WeilConjectures.PurityFiniteSetting
/-- The integer equality for the even shifts of ordered Tate powers.
Source: cohomological shift convention (blueprint: def-pur-finite-reduction-chart-calculus).
Proof: expand the natural-number successor cast and distribute multiplication by two. -/
theorem finiteReductionPowerShift (d : ℕ) :
    (2 * (d : ℤ) + 2) = 2 * ((d + 1 : ℕ) : ℤ) := by
  sorry


/-- Recursion for the ordered tensor powers with their specified even shifts.
All the tensor, shift and root maps are input constructions; no new coherence data
are chosen. Source: blueprint Step 1
(blueprint: def-pur-finite-reduction-chart-calculus). -/
def finiteReductionOrderedPower {C : Type v} [Category.{w} C]
    (T : C ⥤ C ⥤ C) (B : ℕ → C) (U : ℕ → C) (L V : C)
    (z : B 0 ≅ U 0) (t : L ≅ V)
    (s : ∀ n : ℕ, B (n + 1) ≅ (T.obj (B n)).obj L)
    (a : ∀ n : ℕ, (T.obj (U n)).obj V ≅ U (n + 1)) :
    ∀ n : ℕ, B n ≅ U n
  | 0 => z
  | n + 1 => s n ≪≫
    compositionTensorMapIso T (finiteReductionOrderedPower T B U L V z t s a n) t ≪≫ a n

/-- The native even-shift tensor-unit identification, before site specialization.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-chart-calculus). -/
def finiteReductionUnitStepGeneric (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (U : _root_.DerivedCategory C) (z : U ≅ 𝟙_ (_root_.DerivedCategory C)) (n : ℕ) :=
  _root_.DerivedCategory.shiftTensorShiftIso C U U (2 * (n : ℤ)) 2 ≪≫
    (shiftFunctor _ (2 * (n : ℤ) + 2)).mapIso
      (((curriedTensor (_root_.DerivedCategory C)).obj U).mapIso z ≪≫ ρ_ U) ≪≫
    (eqToIso (congrArg (fun a : ℤ ↦ shiftFunctor (_root_.DerivedCategory C) a)
      (finiteReductionPowerShift n))).app U

/-- The published etale tensor's unit-step comparison is the native K-flat one.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-chart-calculus).
Proof: the published tensor is the native derived monoidal tensor. Rewrite this
presentation; the native shift-and-unitor composite gives existence and its
heterogeneous equality fixes the map uniquely. -/
theorem existsUnique_finiteReductionEtaleUnitStep (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (n : ℕ) :
    ∃! a : ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFiniteUnit A X)⟦2 * (n : ℤ)⟧)).obj
          ((Etale.ordinaryFiniteUnit A X)⟦(2 : ℤ)⟧) ≅
      (Etale.ordinaryFiniteUnit A X)⟦2 * ((n + 1 : ℕ) : ℤ)⟧,
      HEq a (finiteReductionUnitStepGeneric
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
          (Etale.ordinaryFiniteUnit A X) (smoothPurityUnitIso A X) n) := by
  sorry

/-- Assemble root charts in the published tensor presentation.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-chart-calculus). -/
def finiteReductionEtalePowerAssembly (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (B : ℕ → Etale.DerivedCategoryModule A X)
    (L : Etale.DerivedCategoryModule A X)
    (z : B 0 ≅ Etale.ordinaryFiniteUnit A X)
    (t : L ≅ (Etale.ordinaryFiniteUnit A X)⟦(2 : ℤ)⟧)
    (s : ∀ n : ℕ, B (n + 1) ≅ ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      (B n)).obj L) (d : ℕ) :=
  finiteReductionOrderedPower (Etale.derivedTensor (ModuleCat.{u + 1} A) X) B
    (fun n ↦ (Etale.ordinaryFiniteUnit A X)⟦2 * (n : ℤ)⟧)
    L ((Etale.ordinaryFiniteUnit A X)⟦(2 : ℤ)⟧)
    (by simpa only [Nat.cast_zero, mul_zero] using
      z ≪≫ ((shiftFunctorZero _ ℤ).app (Etale.ordinaryFiniteUnit A X)).symm) t s
    (fun n ↦ (existsUnique_finiteReductionEtaleUnitStep A X n).choose) d

/-- Assemble the published positive coefficient powers from a given degree-one chart.
The zero and successor maps are the existing ordered-power maps, specialized here
with an abstract coefficient ring before any quotient ring is substituted.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-chart-calculus). -/
def finiteReductionEtaleRootPowerChart (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (X : Scheme.{u})
    (t : (Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ ≅
      (Etale.ordinaryFiniteUnit A X)⟦(2 : ℤ)⟧) (d : ℕ) :
    Etale.affineLinearBaseCoefficient A N hA X d ≅
      (Etale.ordinaryFiniteUnit A X)⟦2 * (d : ℤ)⟧ :=
  finiteReductionEtalePowerAssembly A X
    (Etale.affineLinearBaseCoefficient A N hA X)
    ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
    (eqToIso (compositionEtalePowerZero A N hA X)) t
    (fun n ↦ eqToIso (compositionEtalePowerSuccessor A N hA X n)) d

/-- Exact monoidal inverse image carries the derived unit to the derived unit.
The map is induced by its ordinary monoidal unit, with the exact-derived
single-complex comparison on both sides. Source: blueprint Step 1
(blueprint: def-pur-finite-reduction-chart-calculus). -/
def finiteReductionDerivedUnitGeneric {C D : Type v}
    [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{w} C] [IsGrothendieckAbelian.{w} D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [BraidedCategory C] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso D (ComplexShape.up ℤ))]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Monoidal] : F.mapDerivedCategory.obj (𝟙_ (_root_.DerivedCategory C)) ≅
      𝟙_ (_root_.DerivedCategory D) :=
  F.mapDerivedCategory.mapIso (_root_.DerivedCategory.singleFunctorObjUnitIso C).symm ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app (𝟙_ C) ≪≫
    (_root_.DerivedCategory.singleFunctor D 0).mapIso (Functor.Monoidal.εIso F).symm ≪≫
    _root_.DerivedCategory.singleFunctorObjUnitIso D

/-- The coefficient-unit chart for exact comparison pullback, with its canonical
ordinary monoidal-unit and exact-derived single-object maps.
Source: blueprint finite-reduction proof Step 1
(blueprint: def-pur-finite-reduction-chart-calculus). -/
def finiteReductionComparisonUnitChart (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit A X) ≅
      𝟙_ (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
      (smoothPurityUnitIso A X) ≪≫
    finiteReductionDerivedUnitGeneric
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)

/-- Tensor with the shifted unit, with the K-flat second-variable shift and right unitor.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-chart-calculus). -/
def finiteReductionTensorUnitGeneric (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (M : _root_.DerivedCategory C) (r : ℤ) :=
  letI := _root_.DerivedCategory.commShiftTensorLeft C M
  (((curriedTensor (_root_.DerivedCategory C)).obj M).commShiftIso r).app
      (𝟙_ (_root_.DerivedCategory C)) ≪≫
    (shiftFunctor _ r).mapIso (ρ_ M)

/-- The native K-flat tensor-unit equation, in the published tensor presentation.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-chart-calculus). -/
def FiniteReductionTensorUnitNormalized
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (r : ℤ)
    (a : ((ProEtale.derivedTensor C X).obj M).obj
      ((𝟙_ (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)))⟦r⟧) ≅ M⟦r⟧) : Prop :=
  HEq a (finiteReductionTensorUnitGeneric (Sheaf (Scheme.ProEt.topology X) C) M r)

/-- The published tensor-unit comparison is specified by its native K-flat map.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-chart-calculus).
Proof: rewrite the published tensor with smoothPurityTensorPresentation. The
native tensor-shift comparison followed by the shifted right unitor then has
the required endpoints. Its exact heterogeneous equality gives uniqueness. -/
theorem existsUnique_finiteReductionTensorUnit
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (r : ℤ) :
    ∃! a : ((ProEtale.derivedTensor C X).obj M).obj
        ((𝟙_ (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)))⟦r⟧) ≅ M⟦r⟧,
      FiniteReductionTensorUnitNormalized C X M r a := by
  sorry

/-- The published tensor-unit chart, chosen from its unique native normalization.
The coefficient category is abstract here, so the normalization is not expanded
when a finite quotient ring is substituted.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-chart-calculus). -/
def finiteReductionTensorUnit
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (r : ℤ) :
    ((ProEtale.derivedTensor C X).obj M).obj
      ((𝟙_ (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)))⟦r⟧) ≅ M⟦r⟧ :=
  (existsUnique_finiteReductionTensorUnit C X M r).choose


end WeilConjectures.PurityFiniteSetting
