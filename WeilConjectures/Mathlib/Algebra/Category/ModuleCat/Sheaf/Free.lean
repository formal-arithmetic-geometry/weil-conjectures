/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# The free sheaf of modules on a one-element type

`SheafOfModules.free I` is the coproduct of copies of `SheafOfModules.unit R` indexed by `I`,
so for a one-element type `I` it is the unit itself. This is
`SheafOfModules.freeUniqueIso`, which is how properties proved for the free sheaves of modules
are transported to the structure sheaf.
-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf of modules on a one-element type is the unit. -/
noncomputable def freeUniqueIso (I : Type u) [Unique I] : free (R := R) I ≅ unit R :=
  coproductUniqueIso (fun (_ : I) ↦ unit R)

end SheafOfModules
