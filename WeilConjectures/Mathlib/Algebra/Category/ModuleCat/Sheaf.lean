/-
Copyright (c) 2026 Orchestra Agent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Orchestra Agent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Evaluation of sheaves of modules is additive

Evaluating a sheaf of modules on an object of the site is the composition of the forgetful
functor to presheaves of modules with evaluation of presheaves of modules, both of which are
additive. Since `SheafOfModules.evaluation` is a plain definition, the instance does not fire
by itself and is transported here.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

instance (X : Cᵒᵖ) : (evaluation.{v} R X).Additive :=
  inferInstanceAs (forget R ⋙ PresheafOfModules.evaluation _ X).Additive

end SheafOfModules
