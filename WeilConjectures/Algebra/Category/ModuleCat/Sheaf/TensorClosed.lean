/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree

/-!
# Additivity of the tensor product of sheaves of modules

The monoidal structure on sheaves of modules over a sheaf of commutative rings is additive in
each variable. Together with `SheafOfModules.monoidalClosed` this makes sheaves of modules
additive symmetric monoidal closed.

Source: Stacks Project, Modules on Sites, Section 03EK and Lemma 03EO
(blueprint: lem-pc-sheaf-modules-tensor-closed).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] monoidalCategory symmetricCategory

/-- The tensor product of sheaves of modules over a sheaf of commutative rings is additive in
each variable. Source: Stacks Project, Section 03EK and Lemma 03EO
(blueprint: lem-pc-sheaf-modules-tensor-closed).

Proof: the tensor product is the sheafification of the sectionwise tensor product
[def-pur-sheaf-tensor-product], and sectionwise bilinearity makes tensoring with a fixed sheaf
an additive functor in each variable. -/
instance monoidalPreadditive (R : Sheaf J CommRingCat.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (𝓡 R)) where
  whiskerLeft_zero {X Y Z} := (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := (tensorRight X).map_zero Y Z
  whiskerLeft_add {X _ _} f g := (tensorLeft X).map_add (f := f) (g := g)
  add_whiskerRight {X _ _} f g := (tensorRight X).map_add (f := f) (g := g)

end SheafOfModules
