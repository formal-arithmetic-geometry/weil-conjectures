/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Coproducts of flat sheaves of modules

Source: Stacks Project, Modules on Sites, Lemma 18.28.5, Tag 03EU, clause (2)
(blueprint: lem-pc-sites-modules-coproduct-flat).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- A set-indexed coproduct of flat sheaves of modules over a sheaf of commutative rings
is flat, including the empty coproduct.

Source: Stacks Project, Modules on Sites, Lemma 18.28.5, Tag 03EU, clause (2)
(blueprint: lem-pc-sites-modules-coproduct-flat).

Proof:
1. Use the chosen small site of `def-weil-size-convention`. The category of sheaves of
   modules is Grothendieck abelian by `prop-pur-kinjective-resolutions-exist`, and its
   sheaf tensor product is symmetric monoidal closed by `lem-pc-sheaf-modules-tensor-closed`.
   For each summand, `def-pc-flat-sheaf-modules` gives exactness of tensoring on the right.
   Symmetry transports this to tensoring on the left; hence each summand satisfies the
   abstract flatness condition used in `lem-weil-pbc-flat-coproduct`.
2. Apply `lem-weil-pbc-flat-coproduct`: closedness makes tensor commute with coproducts,
   and coproducts are exact in this Grothendieck abelian category. Tensoring on the left
   with the coproduct preserves finite limits. Symmetry gives the same on the right;
   closedness also gives right exactness. Thus tensoring on the right with the coproduct
   is exact, precisely `def-pc-flat-sheaf-modules`. -/
theorem isFlat_coproduct
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) {B : Type u}
    (M : B → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hflat : ∀ b : B, IsFlat (M b)) : IsFlat (∐ M) := by
  sorry

end SheafOfModules
