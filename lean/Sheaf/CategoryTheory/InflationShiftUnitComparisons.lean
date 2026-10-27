module

public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-! # Canonical monoidal inflation and invariant-adjunction normalization

Source: the internal-action infrastructure associated with paragraph (3) of the current
blueprint's direct-image stability proof; Stacks 015F, 06YY, 07A4, 07A6, 09T5, 0FPT, 0FNH.
The auxiliary normalization is agent-formulated, with an exact external reference wanted.
(blueprint: def-sfb-inflation-shift-unit-comparisons).

The tensor, its unit, its Koszul symmetry, the invariant inclusion and the adjunction
are the existing constructions, rather than existential replacements for those data.
The ordered shifted-unit comparison below allows every integer, including negative ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CondensedBar
open CategoryTheory.CondensedDerivedRestriction
open Profinite.CondensedAction (trivial)

namespace CategoryTheory.CondensedInflationNormalization

variable (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The fixed shift is the termwise signed shift of exact localization.
Source: Stacks 015F (blueprint: def-sfb-inflation-shift-unit-comparisons). -/
instance inflationShift : (trivialDerived A G).CommShift ℤ :=
  inferInstanceAs ((trivial (R := A.toMon) (P := G)).mapDerivedCategory.CommShift ℤ)

/-- The actual regular coefficient object in degree zero.
Source: blueprint paragraph (3)
(blueprint: def-sfb-inflation-shift-unit-comparisons). -/
abbrev baseCoefficient := (DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)

/-- Inflation of the regular coefficient, by exact localization of the single complex.
Source: Stacks 015F (blueprint: def-sfb-inflation-shift-unit-comparisons). -/
def coefficientIso : (trivialDerived A G).obj (baseCoefficient A) ≅ coefficient A G :=
  ((trivial (R := A.toMon) (P := G)).mapDerivedCategorySingleFunctor 0).app
    (Mod.regular A.X)

/-- Inflation of any integer-shifted regular coefficient, with the fixed signed shifts.
Source: Stacks 015F (blueprint: def-sfb-inflation-shift-unit-comparisons). -/
def shiftedCoefficientIso (p : ℤ) :
    (trivialDerived A G).obj ((baseCoefficient A)⟦-p⟧) ≅ (coefficient A G)⟦-p⟧ :=
  ((trivialDerived A G).commShiftIso (-p)).app _ ≪≫
    (shiftFunctor _ (-p)).mapIso (coefficientIso A G)

/-- Ordered extraction of two integer shifts from inverse unit multiplication.
The supplied comparison first extracts the first shift and then the second; the explicit
shift-addition equality changes only the spelling of the source index.
Source: Stacks 0FNH (blueprint: def-sfb-inflation-shift-unit-comparisons). -/
def orderedUnitComparison {D : Type v} [Category.{w} D] [MonoidalCategory D]
    [HasShift D ℤ] (I : D) (e : 𝟙_ D ≅ I) (p q : ℤ)
    (s : I⟦-p⟧ ⊗ I⟦-q⟧ ≅ (I ⊗ I)⟦-p + -q⟧) :
    I⟦-(p + q)⟧ ≅ I⟦-p⟧ ⊗ I⟦-q⟧ :=
  eqToIso (congrArg (fun n : ℤ ↦ I⟦n⟧) (neg_add p q)) ≪≫
    ((shiftFunctor D (-p + -q)).mapIso
      (whiskerRightIso e.symm I ≪≫ λ_ I)).symm ≪≫ s.symm

/-- The prescribed first-then-second comparison in the coefficient category, for all integers.
Source: Stacks 0FNH (blueprint: def-sfb-inflation-shift-unit-comparisons). -/
def baseComparison (p q : ℤ) :
    (baseCoefficient A)⟦-(p + q)⟧ ≅ (baseCoefficient A)⟦-p⟧ ⊗ (baseCoefficient A)⟦-q⟧ :=
  orderedUnitComparison _ (baseUnitIso A) p q
    (DerivedCategory.shiftTensorShiftIso (Modules A) _ _ (-p) (-q))

/-- The identical ordered convention for the action-category regular coefficient.
Source: Stacks 0FNH (blueprint: def-sfb-inflation-shift-unit-comparisons). -/
def actionComparison (p q : ℤ) :
    (coefficient A G)⟦-(p + q)⟧ ≅ (coefficient A G)⟦-p⟧ ⊗ (coefficient A G)⟦-q⟧ :=
  orderedUnitComparison _ (actionUnitIso A G) p q
    (DerivedCategory.shiftTensorShiftIso (Equivariant A G) _ _ (-p) (-q))

/-- The first-variable signed tensor/shift square for the existing strong comparison.
Source: Stacks 07A4 and 0FNH
(blueprint: def-sfb-inflation-shift-unit-comparisons). -/
def FirstShiftSquare : Prop :=
  ∀ (n : ℤ) (M N : DerivedCategory.{u + 1} (Modules A)),
    ((derivedTrivialTensor A G).μIso (M⟦n⟧) N).inv ≫
        (((trivialDerived A G).commShiftIso n).hom.app M ▷ (trivialDerived A G).obj N) ≫
        (((curriedTensor _).flip.obj ((trivialDerived A G).obj N)).commShiftIso n).hom.app
          ((trivialDerived A G).obj M) =
      (trivialDerived A G).map
          ((((curriedTensor _).flip.obj N).commShiftIso n).hom.app M) ≫
        ((trivialDerived A G).commShiftIso n).hom.app (M ⊗ N) ≫
        (((derivedTrivialTensor A G).μIso M N).inv)⟦n⟧'

/-- The second-variable square, separately, with the native signed tensor/shift comparison.
Source: Stacks 07A4 and 0FNH
(blueprint: def-sfb-inflation-shift-unit-comparisons). -/
def SecondShiftSquare : Prop :=
  ∀ (n : ℤ) (M N : DerivedCategory.{u + 1} (Modules A)),
    ((derivedTrivialTensor A G).μIso M (N⟦n⟧)).inv ≫
        ((trivialDerived A G).obj M ◁ ((trivialDerived A G).commShiftIso n).hom.app N) ≫
        (((curriedTensor _).obj ((trivialDerived A G).obj M)).commShiftIso n).hom.app
          ((trivialDerived A G).obj N) =
      (trivialDerived A G).map
          ((((curriedTensor _).obj M).commShiftIso n).hom.app N) ≫
        ((trivialDerived A G).commShiftIso n).hom.app (M ⊗ N) ≫
        (((derivedTrivialTensor A G).μIso M N).inv)⟦n⟧'

/-- Symmetry is measured against the two independently fixed native Koszul braidings.
Source: Stacks 0FPT (blueprint: def-sfb-inflation-shift-unit-comparisons). -/
def SymmetrySquare : Prop :=
  ∀ M N : DerivedCategory.{u + 1} (Modules A),
    ((derivedTrivialTensor A G).μIso M N).inv ≫
        ((DerivedCategory.braidedCategory' (Equivariant A G)).braiding
          ((trivialDerived A G).obj M) ((trivialDerived A G).obj N)).hom =
      (trivialDerived A G).map
          (((DerivedCategory.braidedCategory' (Modules A)).braiding M N).hom) ≫
        ((derivedTrivialTensor A G).μIso N M).inv

end CategoryTheory.CondensedInflationNormalization
