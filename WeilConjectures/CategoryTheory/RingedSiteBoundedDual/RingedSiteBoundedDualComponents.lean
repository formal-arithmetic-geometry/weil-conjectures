/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
public import WeilConjectures.Algebra.Homology.RingedSiteBoundedDualComponents

/-! # Components of the bounded ordinary sheaf dual

Source: Stacks Project, sites-cohomology.tex, Tags 08JJ and 0A8X
(blueprint: lem-sfb-ringed-site-bounded-dual-components).

The abbreviations below only expand the recorded Hom constructions and the
coefficient sheaf in degree zero. The component is the actual product projection.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteBoundedDual

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  (R : Sheaf J CommRingCat.{max c v r})

attribute [local irreducible] homComplexFunctor homComplexπ

end CategoryTheory.RingedSiteBoundedDual
