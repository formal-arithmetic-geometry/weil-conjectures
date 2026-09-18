/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# A shortcut instance for the monoidal structure on cochain complexes

`HomologicalComplex.monoidalCategory` of `Mathlib.Algebra.Homology.Monoidal` makes
`HomologicalComplex A c` monoidal under four `∀`-quantified `GradedObject` hypotheses
(`HasTensor`, `HasTensor₄ObjExt`, `HasGoodTensor₁₂Tensor` and `HasGoodTensorTensor₂₃`). For an
abelian category `A` which is monoidal closed and has colimits all four hold, but only
through the preservation-of-colimits properties that tensoring by a fixed object has
because it is a left adjoint, and instance search has to rediscover that at every use site.

It does not, in practice, get there: with the coefficient category taken to be the category
of étale sheaves of `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, synthesizing
`MonoidalCategory (HomologicalComplex (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))`
exhausts the default budget of 20000 `synthInstance` heartbeats after some 15 seconds, and
had still not finished after ten minutes at twenty times that budget.

This file therefore performs the search once, in a small context where it is immediate, and
records the outcome as an instance, for the shape `ComplexShape.up ℤ` that this development
uses.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

variable (A : Type u) [Category.{v} A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]

/-- Shortcut instance: the cochain complexes of a monoidal closed abelian category with
colimits form a monoidal category. This is `HomologicalComplex.monoidalCategory` with its
`GradedObject` hypotheses discharged once and for all. -/
noncomputable instance HomologicalComplex.monoidalCategoryUp :
    MonoidalCategory (HomologicalComplex A (ComplexShape.up ℤ)) :=
  inferInstance
