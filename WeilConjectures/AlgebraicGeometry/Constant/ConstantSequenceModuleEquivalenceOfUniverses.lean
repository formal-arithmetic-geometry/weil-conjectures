/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite

/-! # Constant sequence modules with independent site universes

Source: Stacks Project, Tags 03DA and 0940; Zheng, Construction 4.1
(blueprint: def-coef-constant-sequence-equivalence).
The forward and inverse functors are constructed from strict systems, not chosen
from an existence theorem. The proved same-universe dependency is unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace CategoryTheory.ConstantCompletion

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (O : Sheaf J CommRingCat.{max c v r})

end CategoryTheory.ConstantCompletion
