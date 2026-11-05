/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Cover-local detection of derived module isomorphisms

Source: Stacks Project, sites-cohomology.tex, Tag 0944, first locality sentence;
categories.tex, localization and cohomology criteria.
(blueprint: lem-weil-pbc-ringed-restriction-local-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

end SheafOfModules
