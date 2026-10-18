/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Grothendieck module sheaves with independent site and coefficient universes

Source: Stacks Project, Modules on Sites, Tags 03CV and 03DA; Cohomology on Sites,
Section 07A5; Injectives, Tag 079Q (blueprint: lem-weil-pbc-ring-sheaves-grothendieck).
-/

@[expose] public section

set_option autoImplicit false

universe c h r s

open CategoryTheory

namespace SheafOfModules

/-- Module sheaves form a Grothendieck abelian category in a common universe containing
both the small site and its ring coefficients. The rings need not be commutative.
Source: Stacks Project, Modules on Sites, Tags 03CV and 03DA; Cohomology on Sites,
Section 07A5; Injectives, Tag 079Q (blueprint: lem-weil-pbc-ring-sheaves-grothendieck).

Proof:
1. Replace the site by its equivalent small category in the common universe and
lift the coefficient rings there. Sectionwise restriction and the inverse lift give
an equivalence of module-sheaf categories; the sheaf condition is invariant under it.
2. On this small site apply SheafOfModules.isGrothendieckAbelian: kernels and filtered
colimits are computed on underlying abelian sheaves, and filtered colimits are exact.
The sheafifications of the free representable modules form a separating family;
their coproduct is a generator. All colimits of the common universe exist.
3. Transport these properties along the equivalence. This gives abelianness, all
small colimits, exact filtered colimits and a generator on the original category. -/
theorem isGrothendieckAbelianOfUniverses
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{r}) :
    IsGrothendieckAbelian.{max c h r s}
      (ringedSiteModules.{max c h r s} R) := by
  sorry

end SheafOfModules
