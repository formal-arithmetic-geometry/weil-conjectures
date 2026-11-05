/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.DerivedModuleCellularFiltration
import WeilConjectures.CategoryTheory.DerivedModuleFiltrationTelescope

/-! # Generation of a module derived category by shifts of the ring

Source: literature/stacks-project/more-algebra.tex, Remark 15.60.11 (Tag 09PB)
(blueprint: lem-pc-derived-module-free-generation).

The property in the conclusion is the semantic description of the smallest full
subcategory containing the shifts of the free rank-one module and closed under
set-indexed coproducts, distinguished triangles, and retracts.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

end CategoryTheory
