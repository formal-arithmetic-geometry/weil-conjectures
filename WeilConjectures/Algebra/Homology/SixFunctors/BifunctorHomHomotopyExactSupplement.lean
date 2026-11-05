/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
import WeilConjectures.Algebra.Homology.BifunctorHomCone
import WeilConjectures.Algebra.Homology.BifunctorHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Opposite.OpOp
public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHomHomotopyExact

/-!
# Exactness of the signed bifunctor Hom complex on the homotopy category

Source: Stacks Project, Tag 08JC, `lemma-RHom-triangulated`, termwise-split Hom argument,
generalized to a separately additive bifunctor; the signed model is
`CochainComplex.bifunctorHomObj` in
`WeilConjectures.Algebra.Homology.BifunctorHomComplex`.
(blueprint: lem-sf-bifunctor-homotopy-exact)

The existing `bifunctorHomHomotopyFunctor H I` takes values in the opposite derived
category. Its `leftOp` is the functor from the opposite homotopy category to the derived
category in the node. The source uses the usual opposite triangulation: its shift by
`m` is the underlying shift by `-m`. The shift structure is existential data, and the
triangulated assertion uses that same structure.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

universe u₁ u₂ u₃ v₁ v₂ v₃ w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.Opposite

namespace CochainComplex

open Opposite CategoryTheory.Category CategoryTheory.Pretriangulated

section ShiftConstruction

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Abelian A] [Abelian B] [Abelian C] [HasCountableProducts C]
  (H : Aᵒᵖ ⥤ B ⥤ C) [H.Additive] [∀ X : Aᵒᵖ, (H.obj X).Additive]
  (I : CochainComplex B ℤ)

variable [HasDerivedCategory.{w} C]

end ShiftConstruction

end CochainComplex
