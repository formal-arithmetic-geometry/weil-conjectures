/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!

# Bounded objects of a derived category with cohomology in a given class

Let `A` be an abelian category and `P` a property of objects of `A` (for instance,
constructibility of a sheaf of modules). We define the property
`DerivedCategory.boundedWithHomology P` of objects `K` of `D(A)`:

1. `K` is bounded, i.e. `H^i(K) = 0` for `i` outside a finite interval `[a, b]`
   (`DerivedCategory.mem_bounded_iff`);
2. every cohomology object `H^i(K)` satisfies `P`.

The corresponding full subcategory of `D(A)` is `DerivedCategory.BoundedWithHomology P`. Its
morphisms are the morphisms of `D(A)`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- An object of the derived category is bounded (for the canonical t-structure) iff its
cohomology vanishes outside a finite interval. -/
lemma mem_bounded_iff (K : DerivedCategory A) :
    TStructure.t.bounded K ↔ ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((homologyFunctor A i).obj K) := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a, b, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (isGE_iff K a).1 ha i hi
    · exact (isLE_iff K b).1 hb i hi
  · rintro ⟨a, b, h⟩
    exact ⟨⟨a, (isGE_iff K a).2 fun i hi ↦ h i (Or.inl hi)⟩,
      ⟨b, (isLE_iff K b).2 fun i hi ↦ h i (Or.inr hi)⟩⟩

variable (P : ObjectProperty A)

/-- The objects of the derived category all of whose cohomology objects satisfy `P`. -/
def homologyMem : ObjectProperty (DerivedCategory A) :=
  fun K ↦ ∀ n : ℤ, P ((homologyFunctor A n).obj K)

/-- The bounded objects of the derived category all of whose cohomology objects
satisfy `P`. -/
def boundedWithHomology : ObjectProperty (DerivedCategory A) :=
  TStructure.t.bounded ⊓ homologyMem P

/-- The full subcategory of the derived category consisting of bounded objects all of whose
cohomology objects satisfy `P`. -/
abbrev BoundedWithHomology : Type _ := (boundedWithHomology P).FullSubcategory

/-- The inclusion of `BoundedWithHomology P` in the derived category, which is fully
faithful. -/
noncomputable abbrev BoundedWithHomology.ι : BoundedWithHomology P ⥤ DerivedCategory A :=
  (boundedWithHomology P).ι

end DerivedCategory
