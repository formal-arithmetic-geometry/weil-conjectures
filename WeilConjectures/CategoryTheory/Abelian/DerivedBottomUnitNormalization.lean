/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.Abelian.DerivedBottomUnitNormalizationFormula

/-! # Normalization of the bottom-cohomology comparison

Source: Stacks Project, Tag 05TC (2), and the degree-zero comparison for a left
exact derived functor, as used in Tags 08D4 and 0AVW.
(blueprint: lem-pc-derived-bottom-unit-normalization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

end CategoryTheory.Functor
