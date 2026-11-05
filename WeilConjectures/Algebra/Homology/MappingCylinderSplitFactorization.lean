/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Mapping-cylinder split factorization of a cochain map

Source: Stacks Project, Derived Categories, Lemma 013N, Definition 014G, and Remark 013O.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

end CochainComplex
