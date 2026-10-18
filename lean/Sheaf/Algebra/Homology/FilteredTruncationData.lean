/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Algebra.Homology.FilteredDerivedHomCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated

/-!
# Universal truncation triangles for finite filtered derived categories

Source: Varshavsky--Lefschetz--Verdier trace formula, §§5.1.1--5.1.2,
pp. 39--40 (blueprint: def-trf-filtered-truncation-data).
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex.FiniteFiltered

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The complete package of functors and universal properties asserted for the
bounded-below finite-filtered localization. The forgetful functor `omega` and the graded
functors `gr p` are pinned on representatives to the underlying and graded complexes
(`omegaComparison`, `grComparison`), and `grade_truncation` is normalized by the
canonical projection `FᵖK → grᵖK`.
Source: Varshavsky, §§5.1.1--5.1.2 (blueprint: def-trf-filtered-truncation-data). -/
structure FilteredTruncationData where
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
  unique_triangle : ∀ (p : ℤ) (M L R : Derived (A := A) false)
    (i : L ⟶ M) (q : M ⟶ R) (d : R ⟶ L⟦(1 : ℤ)⟧),
    Triangle.mk i q d ∈ distTriang (Derived (A := A) false) →
    (∀ a : ℤ, a < p → IsZero ((gr a).obj L)) →
    (∀ a : ℤ, p ≤ a → IsZero ((gr a).obj R)) →
    ∃! e : Triangle.mk ((inclusion p).app M) ((quotient p).app M)
        ((connecting p).app M) ≅ Triangle.mk i q d,
      e.hom.hom₂ = 𝟙 M
  high_hom_bijective : ∀ (p : ℤ) (L M : Derived (A := A) false),
    (∀ a : ℤ, a < p → IsZero ((gr a).obj L)) →
    Function.Bijective (fun f : L ⟶ (high p).obj M =>
      f ≫ (inclusion p).app M)
  low_hom_bijective : ∀ (p : ℤ) (M R : Derived (A := A) false),
    (∀ a : ℤ, p ≤ a → IsZero ((gr a).obj R)) →
    Function.Bijective (fun f : (low p).obj M ⟶ R =>
      (quotient p).app M ≫ f)
  high_hom_natural : ∀ (p : ℤ) (L L' M M' : Derived (A := A) false)
    (f : L' ⟶ L) (g : M ⟶ M') (h : L ⟶ (high p).obj M),
    f ≫ h ≫ (high p).map g ≫ (inclusion p).app M' =
      f ≫ (h ≫ (inclusion p).app M) ≫ g
  low_hom_natural : ∀ (p : ℤ) (M M' R R' : Derived (A := A) false)
    (f : M' ⟶ M) (g : R ⟶ R') (h : (low p).obj M ⟶ R),
    (quotient p).app M' ≫ (low p).map f ≫ h ≫ g =
      f ≫ (quotient p).app M ≫ h ≫ g
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
  pure : ∀ (_p : ℤ), ObjectProperty (Derived (A := A) false)
  pure_iff : ∀ (p : ℤ) (M : Derived (A := A) false),
    pure p M ↔ ∀ a : ℤ, a ≠ p → IsZero ((gr a).obj M)
  place : ∀ (p : ℤ), DerivedCategory.Plus A ⥤
    (pure p).FullSubcategory
  place_equivalence : ∀ (p : ℤ), (place p).IsEquivalence
  place_forget : ∀ (p : ℤ),
    place p ⋙ ObjectProperty.ι (pure p) ⋙ omega ≅ 𝟭 _
  place_grade : ∀ (p a : ℤ) (K : DerivedCategory.Plus A), a ≠ p →
    IsZero ((gr a).obj ((place p).obj K).obj)


end CochainComplex.FiniteFiltered
