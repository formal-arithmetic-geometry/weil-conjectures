/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Component-normalized global cochains of the sheaf Hom complex

Source: Stacks Project, Cohomology on Sites, Section 21.34, Equation (21.34.0.2)
(Tag 0A8Z), and Lemma 21.34.8 (Tag 0A96).
(blueprint: lem-pc-normalized-hom-complex-global-cochains)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" =>
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "Mod" => SheafOfModules.{u} 𝓡

end CategoryTheory
