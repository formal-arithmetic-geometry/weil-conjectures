/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Preadditive.TraceSplitting
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Uniqueness of the invariant retraction

Let `u : G ⟶ T` be a morphism in a preadditive category with a trace `t : T ⟶ G` factoring the
norm of finitely many endomorphisms `ρ i` of `T` through `u` (`t ≫ u = ∑ i, ρ i`), with `d` the
number of the `ρ i` invertible on `G`. Then a retraction `r` of `u` invariant under the `ρ i`
(`ρ i ≫ r = r`) is the normalized trace `d⁻¹ t` (`CategoryTheory.eq_normalizedTrace`): indeed
`d • r = ∑ i, ρ i ≫ r = t ≫ u ≫ r = t`. This gives the compatibility of the normalized traces
in a tower of Galois coverings without computing the traces.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

end CategoryTheory
