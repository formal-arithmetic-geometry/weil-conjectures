/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.Derived.DerivedPerfectSmallClass
import WeilConjectures.CategoryTheory.Perfect.PerfectFamilyLocalizingHull

/-! # Perfect families in set-generated derived subcategories

Source: Neeman, Theorem 0.2; Krause, Localization theory, Theorem 7.2.1.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- A set-generated localizing subcategory of a Grothendieck derived category admits
small, shift-closed perfect generators.

Source: Neeman, *On the derived category of sheaves on a manifold*, Theorem 0.2.
-/
theorem setGeneratedDerived_exists_perfectFamily
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (P Q : ObjectProperty (DerivedCategory A))
    [ObjectProperty.EssentiallySmall.{v} P]
    [Q.IsClosedUnderIsomorphisms] [Q.IsTriangulated]
    [∀ I : Type v, Q.IsClosedUnderColimitsOfShape (Discrete I)]
    (hP : P ≤ Q)
    (hminimal : ∀ R : ObjectProperty (DerivedCategory A), P ≤ R →
      R.IsClosedUnderIsomorphisms → R.IsTriangulated →
      (∀ I : Type v, R.IsClosedUnderColimitsOfShape (Discrete I)) → Q ≤ R) :
    ∃ (J : Type v) (S : J → Q.FullSubcategory),
      (∀ (j : J) (n : ℤ), ∃ k, Nonempty (S k ≅ (S j)⟦n⟧)) ∧
      (∀ X (_hX : P X), ∃ j, Nonempty (X ≅ (S j).obj)) ∧
      (∀ (I : Type v) (X Y : I → Q.FullSubcategory) (f : ∀ i, X i ⟶ Y i),
        (∀ i j, Function.Surjective (fun g : S j ⟶ X i ↦ g ≫ f i)) →
        ∀ j, Function.Surjective (fun g : S j ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f)) := by
  obtain ⟨S, hSs, hSi, hSt, hPS, hperfect, hsub⟩ :=
    derived_exists_perfectSmallClass P
  have := hSs
  have := hSi
  have := hSt
  let B := S ⊓ Q
  have : ObjectProperty.EssentiallySmall.{v} B :=
    ObjectProperty.EssentiallySmall.of_le (Q := S) inf_le_left
  have hsmall (U : DerivedCategory A) (hU : S U) (I : Type v)
      (Y : I → DerivedCategory A) (hY : ∀ i, B (Y i)) (f : U ⟶ ∐ Y) :
      ∃ V, B V ∧ ∃ (g : U ⟶ V) (h : V ⟶ ∐ Y), g ≫ h = f := by
    obtain ⟨J, a, hS, g, hg⟩ := hsub I Y (fun i ↦ (hY i).1) U hU f
    have hQ : Q (∐ fun j ↦ Y (a j)) :=
      Q.prop_of_isColimit (coproductIsCoproduct (fun j ↦ Y (a j)))
        (fun j ↦ (hY (a j.as)).2)
    exact ⟨_, ⟨hS, hQ⟩, g, _, hg⟩
  exact perfectFamily_of_small_hull S B inf_le_left P Q
    (fun X hX ↦ ⟨hPS X hX, hP X hX⟩) inf_le_right hminimal hperfect hsmall

end CategoryTheory
