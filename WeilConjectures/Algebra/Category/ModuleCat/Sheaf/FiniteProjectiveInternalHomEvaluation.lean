/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Evaluation for a finite projective sheaf of modules

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of
`lemma-dual-perfect-complex`, finite-free and direct-summand calculation.
(blueprint: lem-pc-finite-projective-internal-hom-evaluation).
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SheafOfModules

attribute [local instance] monoidalCategory symmetricCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

end SheafOfModules
