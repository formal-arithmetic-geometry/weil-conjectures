module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Limit cone for a K-injective tower
Source: Mathlib, CategoryTheory.Limits.hasLimit_of_equalizer_and_product
(blueprint: lem-weil-derived-limit-tower-core-cone). -/

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Existence of a limit cone for a K-injective tower.
Source: Mathlib, `Limits.hasLimit_of_equalizer_and_product` (Stacks Tag 002N).
Proof: countable products in A induce countable products of cochain complexes.
The object and arrow index types of the natural-number tower are countable.
An abelian category of complexes has equalizers. Mathlib's construction of a
limit as an equalizer of two product maps therefore supplies a limit cone.
No K-injectivity or exactness is needed for this part of the argument.
(blueprint: lem-weil-derived-limit-tower-core-cone). -/
theorem derivedCategory_towerLimit_cone
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (hP : HasCountableProducts (DerivedCategory A)) :
    letI : HasCountableProducts (DerivedCategory A) := hP
    ∀ (_ : EnoughInjectives A)
      (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
      ∃ c : Cone I.asFunctor, Nonempty (IsLimit c) := by
  intro hI I hKI
  have : HasCountableProducts (CochainComplex A ℤ) := ⟨fun _ ↦ inferInstance⟩
  have : HasLimit I.asFunctor := hasLimit_of_equalizer_and_product I.asFunctor
  exact ⟨limit.cone I.asFunctor, ⟨limit.isLimit I.asFunctor⟩⟩

end CategoryTheory
