/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.Order.Directed

/-!
# The poset of finite coefficient fields

Fix a prime `ℓ` and the algebraic closure `ℚ̄_ℓ = AlgebraicClosure ℚ_[ℓ]`. This file
introduces the index of the `ℓ`-adic coefficient formalism: the poset

`FinExt ℓ = { E | ℚ_ℓ ⊆ E ⊆ ℚ̄_ℓ, [E : ℚ_ℓ] < ∞ }`

of finite subextensions, ordered by inclusion. Two facts about it drive the whole
construction of `Dᵇ_c(Y, ℚ̄_ℓ)`:

- it is **directed** (`FinExt.instIsDirectedOrder`): the compositum of two finite
  subextensions is again finite. This is what lets finitely many objects, morphisms and
  equations be transported to one common coefficient field, and it is the only property of
  the index used by the common-stage construction of
  `WeilConjectures.CategoryTheory.DerivedCategory.QlbarCoefficient.CommonStage.Defs`;
- **every scalar is defined at some stage** (`FinExt.exists_mem_subring`): an element of
  `ℚ̄_ℓ` is algebraic over `ℚ_ℓ`, hence lies in a finite subextension. This is what makes
  the `Hom` groups of the common-stage category `ℚ̄_ℓ`-vector spaces, and it is the
  `exists_mem` field of
  `CategoryTheory.TransitionSystem.ScalarSystem`.

Each stage also carries its valuation ring `𝒪_E` (`FinExt.integers`), the coefficient ring
of the integral stage `Dᵇ_c(Y, 𝒪_E)`.
-/

@[expose] public section

universe u

open scoped IntermediateField

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- A finite subextension of `ℚ̄_ℓ / ℚ_ℓ`: an intermediate field which is
finite-dimensional over `ℚ_ℓ`. These are the coefficient fields of the `ℓ`-adic
formalism. -/
structure FinExt where
  /-- The underlying intermediate field. -/
  toIntermediateField : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])
  /-- It is finite over `ℚ_ℓ`. -/
  finiteDimensional : FiniteDimensional ℚ_[ℓ] toIntermediateField

namespace FinExt

variable {ℓ}

attribute [instance] FinExt.finiteDimensional

@[ext]
lemma ext {E F : FinExt ℓ} (h : E.toIntermediateField = F.toIntermediateField) : E = F := by
  cases E; cases F; simpa using h

lemma toIntermediateField_injective :
    Function.Injective (FinExt.toIntermediateField (ℓ := ℓ)) := fun _ _ h ↦ ext h

noncomputable instance : PartialOrder (FinExt ℓ) :=
  PartialOrder.lift _ toIntermediateField_injective

lemma le_iff {E F : FinExt ℓ} :
    E ≤ F ↔ E.toIntermediateField ≤ F.toIntermediateField := Iff.rfl

/-- The compositum of two finite subextensions, again a finite subextension. -/
noncomputable def sup (E F : FinExt ℓ) : FinExt ℓ where
  toIntermediateField := E.toIntermediateField ⊔ F.toIntermediateField
  finiteDimensional := inferInstance

lemma le_sup_left (E F : FinExt ℓ) : E ≤ E.sup F := le_iff.mpr _root_.le_sup_left
lemma le_sup_right (E F : FinExt ℓ) : F ≤ E.sup F := le_iff.mpr _root_.le_sup_right

/-- The poset of finite subextensions is directed: any two are contained in their
compositum, which is again finite over `ℚ_ℓ`. -/
instance : IsDirectedOrder (FinExt ℓ) :=
  ⟨fun E F ↦ ⟨E.sup F, E.le_sup_left F, E.le_sup_right F⟩⟩

instance : Nonempty (FinExt ℓ) := ⟨⟨⊥, inferInstance⟩⟩

section Subring

variable (ℓ)

/-- The coefficient field of the stage `E`, as a subring of `ℚ̄_ℓ`. This is the family
`k` of `CategoryTheory.TransitionSystem.ScalarSystem`. -/
noncomputable def subring (E : FinExt ℓ) : Subring (AlgebraicClosure ℚ_[ℓ]) :=
  E.toIntermediateField.toSubalgebra.toSubring

variable {ℓ}

@[simp]
lemma mem_subring {E : FinExt ℓ} {α : AlgebraicClosure ℚ_[ℓ]} :
    α ∈ subring ℓ E ↔ α ∈ E.toIntermediateField := Iff.rfl

lemma subring_mono : Monotone (subring ℓ) := fun _ _ h _ hx ↦ h hx

/-- Every element of `ℚ̄_ℓ` is defined over some finite subextension: it is algebraic over
`ℚ_ℓ`, so it lies in the finite subextension it generates. -/
lemma exists_mem_subring (α : AlgebraicClosure ℚ_[ℓ]) : ∃ E : FinExt ℓ, α ∈ subring ℓ E := by
  have hα : IsIntegral ℚ_[ℓ] α := Algebra.IsIntegral.isIntegral α
  exact ⟨⟨ℚ_[ℓ]⟮α⟯, IntermediateField.adjoin.finiteDimensional hα⟩,
    IntermediateField.mem_adjoin_simple_self _ _⟩

end Subring

section Integers

/-- The valuation ring `𝒪_E` of the coefficient field `E`: the integral closure of `ℤ_ℓ`
in `E`. This is the coefficient ring of the integral stage `Dᵇ_c(Y, 𝒪_E)`. -/
def integers (E : FinExt ℓ) : Type :=
  integralClosure ℤ_[ℓ] E.toIntermediateField

noncomputable instance (E : FinExt ℓ) : CommRing E.integers :=
  inferInstanceAs <| CommRing (integralClosure ℤ_[ℓ] E.toIntermediateField)

/-- `𝒪_E` lifted to the universe of the base schemes, so that it can be used as the
coefficient ring of sheaves of modules on the pro-étale site of a `Scheme.{u}`. -/
def integersULift (E : FinExt ℓ) : Type u := ULift.{u} E.integers

noncomputable instance (E : FinExt ℓ) : CommRing (integersULift.{u} E) :=
  inferInstanceAs <| CommRing (ULift.{u} E.integers)

end Integers

end FinExt
