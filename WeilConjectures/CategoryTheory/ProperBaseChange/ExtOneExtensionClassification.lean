/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Degree-one Ext classes classify short exact extensions

Source: Stacks Project, Derived Categories, Tags 06XU and 06XV; exact-functor compatibility
by Tags 0151 and 0152 (blueprint: lem-weil-pbc-ext-one-extension-classification).
-/

@[expose] public section

universe w w' t t' v v' u u'

open CategoryTheory.Limits

namespace CategoryTheory

open Category _root_.DerivedCategory Pretriangulated

end CategoryTheory
