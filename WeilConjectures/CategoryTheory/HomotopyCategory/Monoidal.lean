/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal

/-!
# A shortcut instance for the monoidal structure on the homotopy category

The monoidal structure on `HomotopyCategory A c` of
`WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal` is induced by the one
on cochain complexes, and carries the same four `∀`-quantified `GradedObject` hypotheses,
plus `HasMapBifunctor` on top of them. As for cochain complexes (see
`WeilConjectures.Mathlib.Algebra.Homology.Monoidal`), instance search does not get through
them at the use sites of this development: for the category of étale sheaves of
`WeilConjectures.SixFunctors.Etale.Derived.Tensor`, synthesizing
`MonoidalCategory (HomotopyCategory (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))`
exhausts the default budget of 20000 `synthInstance` heartbeats after some 15 seconds.

This file therefore performs the search once, in a small context, and records the outcome as
an instance, for the shape `ComplexShape.up ℤ` that this development uses. Even here the
search needs the `have` in the proof: without `X₁.HasTensor X₂` put in the local context
first, it fails.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

variable (A : Type u) [Category.{v} A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]

/-- Shortcut instance: the homotopy category of a monoidal closed abelian category with
colimits is monoidal, the tensor product being the one induced by the tensor product of
cochain complexes. -/
noncomputable instance HomotopyCategory.monoidalCategoryUp :
    MonoidalCategory (HomotopyCategory A (ComplexShape.up ℤ)) :=
  have (X₁ X₂ : GradedObject ℤ A) : X₁.HasTensor X₂ := inferInstance
  inferInstance
