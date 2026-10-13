module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

import Mathlib.Data.Countable.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Limit cone for a tower of complexes
Source: Mathlib, CategoryTheory.Limits.hasLimit_of_equalizer_and_product
(blueprint: lem-weil-derived-limit-tower-core-cone). -/

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Existence of a limit cone for a tower of complexes.
Source: Mathlib, `Limits.hasLimit_of_equalizer_and_product` (Stacks Tag 002N).
Proof: countable products in A induce countable products of cochain complexes.
The object and arrow index types of the natural-number tower are countable.
Equalizers in A induce equalizers of complexes. Mathlib's construction of a
limit as an equalizer of two product maps therefore supplies a limit cone.
No K-injectivity or exactness is needed for this part of the argument.
(blueprint: lem-weil-derived-limit-tower-core-cone). -/
theorem derivedCategory_towerLimit_cone
    (A : Type u) [Category.{v} A] [HasZeroMorphisms A]
    [HasCountableProducts A] [HasEqualizers A] :
    ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
      ∃ c : Cone I.asFunctor, Nonempty (IsLimit c) := by
  intro I
  let : HasCountableProducts (CochainComplex A ℤ) :=
    ⟨fun _ ↦ inferInstance⟩
  let : HasLimit I.asFunctor := hasLimit_of_equalizer_and_product I.asFunctor
  exact ⟨limit.cone _, ⟨limit.isLimit _⟩⟩

end CategoryTheory
