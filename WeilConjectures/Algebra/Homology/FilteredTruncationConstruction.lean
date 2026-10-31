/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FilteredDerivedHomCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated

/-!
# Normalized truncation construction before universal properties

Source: Varshavsky--Lefschetz--Verdier trace formula, §§5.1.1--5.1.2,
pp. 39--40 (blueprint: lem-trf-filtered-truncation-construction).
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex.FiniteFiltered

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Cone-normalized filtration truncation functors, their actual representative maps,
and the canonical single-grade subquotient, before the universal Hom properties.
Source: Varshavsky §§5.1.1--5.1.2 (blueprint: lem-trf-filtered-truncation-construction). -/
structure FilteredTruncationCore where
  [model : TriangulatedLocalization A false]
  omega : Derived (A := A) false ⥤ DerivedCategory.Plus A
  [omega_shift : omega.CommShift ℤ]
  [omega_exact : omega.IsTriangulated]
  omegaComparison : Q false ⋙ omega ⋙ DerivedCategory.Plus.ι (C := A) ≅
    forget false ⋙ DerivedCategory.Q
  gr : ℤ → Derived (A := A) false ⥤ DerivedCategory.Plus A
  grComparison : ∀ p : ℤ, Q false ⋙ gr p ⋙ DerivedCategory.Plus.ι (C := A) ≅
    graded false p ⋙ DerivedCategory.Q
  [gr_shift : ∀ p : ℤ, (gr p).CommShift ℤ]
  [gr_exact : ∀ p : ℤ, (gr p).IsTriangulated]
  high : ℤ → Derived (A := A) false ⥤ Derived (A := A) false
  low : ℤ → Derived (A := A) false ⥤ Derived (A := A) false
  [high_shift : ∀ p : ℤ, (high p).CommShift ℤ]
  [low_shift : ∀ p : ℤ, (low p).CommShift ℤ]
  [high_exact : ∀ p : ℤ, (high p).IsTriangulated]
  [low_exact : ∀ p : ℤ, (low p).IsTriangulated]
  inclusion : ∀ p : ℤ, high p ⟶ 𝟭 _
  quotient : ∀ p : ℤ, 𝟭 _ ⟶ low p
  connecting : ∀ p : ℤ, low p ⟶ high p ⋙ CategoryTheory.shiftFunctor _ (1 : ℤ)
  distinguished : ∀ (p : ℤ) (M : Derived (A := A) false),
    Triangle.mk ((inclusion p).app M) ((quotient p).app M) ((connecting p).app M) ∈
      distTriang (Derived (A := A) false)
  high_support : ∀ (p a : ℤ) (M : Derived (A := A) false), a < p →
    IsZero ((gr a).obj ((high p).obj M))
  low_support : ∀ (p a : ℤ) (M : Derived (A := A) false), p ≤ a →
    IsZero ((gr a).obj ((low p).obj M))
  high_comparison : ∀ (p : ℤ) (K : Complex A false),
    (high p).obj ((Q false).obj K) ≅
      (Q false).obj (CochainComplex.FiniteFiltered.high false K p)
  low_comparison : ∀ (p : ℤ) (K : Complex A false),
    (low p).obj ((Q false).obj K) ≅
      (Q false).obj (CochainComplex.FiniteFiltered.low false K p)
  high_normalization : ∀ (p : ℤ) (K : Complex A false),
    (high_comparison p K).hom ≫ (Q false).map (highι false K p) =
      (inclusion p).app ((Q false).obj K)
  low_normalization : ∀ (p : ℤ) (K : Complex A false),
    (quotient p).app ((Q false).obj K) ≫ (low_comparison p K).hom =
      (Q false).map (lowπ false K p)
  grade_truncation : ∀ (p : ℤ),
    (low (p + 1) ⋙ high p) ⋙ omega ≅ gr p
  grade_normalization : ∀ (p : ℤ) (K : Complex A false),
    (DerivedCategory.Plus.ι (C := A)).map
        (omega.map ((high p).map ((quotient (p + 1)).app ((Q false).obj K))) ≫
          (grade_truncation p).hom.app ((Q false).obj K)) ≫
        (grComparison p).hom.app K =
      (DerivedCategory.Plus.ι (C := A)).map (omega.map (high_comparison p K).hom) ≫
        omegaComparison.hom.app (CochainComplex.FiniteFiltered.high false K p) ≫
          DerivedCategory.Q.map (K.obj.filtration.complexQuotientπ p (p + 1) (by omega))

attribute [instance] FilteredTruncationCore.omega_shift
  FilteredTruncationCore.omega_exact FilteredTruncationCore.gr_shift
  FilteredTruncationCore.gr_exact FilteredTruncationCore.high_shift
  FilteredTruncationCore.low_shift FilteredTruncationCore.high_exact
  FilteredTruncationCore.low_exact

/-- The chain-level inclusion and quotient give exact truncations on the localization.
Source: Varshavsky §§5.1.1(a)--(e), 5.1.2(a)--(c), pp.39--40.
Proof: pass from filtered complexes to filtered homotopy classes using the cylinder.
The uniformly finite bounded-below subcategory is closed under shifts and cones.
The graded-acyclic objects form a triangulated subcategory; its cone class is precisely
the graded quasi-isomorphisms, so its Verdier localization supplies the cone-normalized
triangulation. Forgetting inverts this class by finite filtration induction, and each
graded functor does so by definition. The filtration step and quotient commute with
shifts and cones and preserve graded quasi-isomorphisms: their grades are the original
grades on their support and zero elsewhere. Descend these functors and the actual
inclusion and projection. The cone of the inclusion maps by a graded quasi-isomorphism
to the quotient, yielding the distinguished triangle and its natural connecting map.
Finally the underlying single-grade subquotient is F^p/F^(p+1); its quotient map gives
the natural graded comparison and the displayed normalization.
(blueprint: lem-trf-filtered-truncation-construction). -/
theorem filteredTruncationCore : Nonempty (FilteredTruncationCore A) := by
  sorry

end CochainComplex.FiniteFiltered
