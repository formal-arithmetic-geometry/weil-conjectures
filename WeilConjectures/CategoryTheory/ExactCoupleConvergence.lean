/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCouple
public import WeilConjectures.CategoryTheory.PBCFiltration

import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.SubobjectHomologyStep

/-!
# Convergence of bigraded exact couples

Source: blueprint, def-sp-convergence; Stacks Project, Homology, Sections 12.20 and 12.21,
and Definition 12.24.9 (Tag 012U) (blueprint: def-sp-convergence).

The natural-number index `r` below represents page `r + 2`. Colimits and inverse limits
are expressed by their universal properties on the consecutive arrows of the integer chain.
No infinite (co)limits or complete lattice of subobjects are assumed in the ambient category.
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

-- The subobjects are explicit pullbacks/images. Only their unique kernel lift is chosen:
-- its composite with the monomorphic kernel inclusion is specified by `comm`.

end CategoryTheory.BigradedExactCouple
