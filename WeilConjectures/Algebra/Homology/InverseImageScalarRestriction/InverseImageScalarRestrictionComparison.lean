/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Inverse image and restriction of scalars

The comparison is fixed by the underlying inverse image of sheaves of sets.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03DA.
(blueprint: lem-pur-inverse-image-scalar-restriction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w uT vT uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
namespace SheafOfModules.InverseImageScalarRestriction

end SheafOfModules.InverseImageScalarRestriction
