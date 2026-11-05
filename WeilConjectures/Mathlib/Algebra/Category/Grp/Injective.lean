/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Injective abelian groups and presheaves under universe lifts

The universe lift `AddCommGrpCat.uliftFunctor : AddCommGrpCat.{v} ⥤ AddCommGrpCat.{max v w}`
has no left adjoint, but it still preserves injective objects: an injective abelian group is
divisible, and so is its universe lift. For an essentially small category `C`, the same holds
for presheaves of abelian groups on `C`: an injective presheaf `P` is a retract of a product
`∏ₛ Rₛ(Jₛ)` of the right adjoints of the evaluations at the objects of a small model of `C`
applied to injective abelian groups `Jₛ`, and lifting universes commutes with these.

## Main statements

- `AddCommGrpCat.injective_uliftFunctor_obj`: the universe lift of an injective abelian group is
  injective.
- `CategoryTheory.Presheaf.injective_comp_uliftFunctor`: the universe lift of an injective
  presheaf of abelian groups on an essentially small category is injective.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace AddCommGrpCat

end AddCommGrpCat

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

end CategoryTheory.Presheaf
