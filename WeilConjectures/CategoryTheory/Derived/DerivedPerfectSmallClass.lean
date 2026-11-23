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
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.Derived.DerivedPerfectSmallClassCore
import WeilConjectures.CategoryTheory.Derived.DerivedPerfectSmallClassProperties

/-! # Small perfect classes in Grothendieck derived categories

Source: Neeman, On the derived category of sheaves on a manifold, Theorem 0.2.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Every small family in D(A) lies in an essentially small replete triangulated
perfect class, with bounded-subcoproduct factorization for its own objects.

Source: Neeman, *On the derived category of sheaves on a manifold*, Theorem 0.2.
-/
theorem derived_exists_perfectSmallClass
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (P : ObjectProperty (DerivedCategory A))
    [ObjectProperty.EssentiallySmall.{v} P] :
    ∃ S : ObjectProperty (DerivedCategory A),
      ObjectProperty.EssentiallySmall.{v} S ∧ S.IsClosedUnderIsomorphisms ∧
      S.IsTriangulated ∧ P ≤ S ∧
      (∀ (I : Type v) (X Y : I → DerivedCategory A) (f : ∀ i, X i ⟶ Y i),
        (∀ i U, S U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) →
        ∀ U, S U → Function.Surjective
          (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f)) ∧
      (∀ (I : Type v) (Y : I → DerivedCategory A), (∀ i, S (Y i)) →
        ∀ (U : DerivedCategory A), S U → ∀ f : U ⟶ ∐ Y,
        ∃ (J : Type v) (a : J → I), S (∐ fun j ↦ Y (a j)) ∧
          ∃ g : U ⟶ ∐ fun j ↦ Y (a j),
            g ≫ Sigma.desc (fun j ↦ Sigma.ι Y (a j)) = f) := by
  obtain ⟨S, α, hα, hS, hSi, hSt, hPS, hSsum, hcompact⟩ :=
    derived_exists_perfectSmallClass_core P
  let _ : Fact α.IsRegular := hα
  obtain ⟨hperfect, hfactor⟩ :=
    derived_perfectSmallClass_properties S α hSsum hcompact
  exact ⟨S, hS, hSi, hSt, hPS, hperfect, hfactor⟩

end CategoryTheory
