/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso

/-!
# Scalar extension along an isomorphism of ring sheaves

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03EK and 03CY
(blueprint: lem-weil-sheaf-scalar-extension-ring-iso).

The transported module functor is the existing restriction of scalars along the inverse.
The tensor convention in the existing change-of-rings construction puts the scalar first:
`s ⊗ x` represents the node's `x ⊗ s` under tensor symmetry.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory
open scoped ChangeOfRings

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasWeakSheafify J AddCommGrpCat.{max r m}]
  {R S : Sheaf J CommRingCat.{r}}

end SheafOfModules
