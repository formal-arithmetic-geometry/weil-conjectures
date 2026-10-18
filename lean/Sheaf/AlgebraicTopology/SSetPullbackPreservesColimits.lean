/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Pullback of simplicial sets preserves slice colimits

Source: Charles Rezk, Fibrations and Homotopy Colimits of Simplicial Sheaves,
Proposition 3.7, printed page 6 (blueprint: lem-coef-sset-pullback-preserves-colimits).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace SSet

/-- For any simplicial map, strict pullback between its slices preserves all small colimits.
Source: Charles Rezk, Fibrations and Homotopy Colimits of Simplicial Sheaves,
Proposition 3.7, printed page 6 (blueprint: lem-coef-sset-pullback-preserves-colimits).

Proof:
1. Regard a simplicial set as a presheaf on the simplex category. For every simplex degree,
   [lem-coef-small-set-colimit-quotient] gives the set colimit of the degreewise diagram,
   including the empty diagram. The sectionwise presheaf-colimit result
   [lem-weil-pbc-presheaf-colimits-sectionwise] assembles these sets into a simplicial set.
2. The structure maps to the fixed base form a cocone, and the universal property of
   [def-weil-pbc-category-colimit] gives the induced map to the base and the slice colimit.
   The same argument applies over the source of `p`.
3. Degreewise pairs `(e, x)` with equal images in the base form the strict pullbacks, and
   the simplicial operators and diagram maps act componentwise. This is the strict
   pullback construction used by `Over.pullback p`.
4. The induced comparison sends `[i, (e, x)]` to `(e, [i, x])`. It is surjective by the
   representative clause of [lem-coef-small-set-colimit-quotient], including the empty case.
5. Equality of two images gives a finite chain of generating arrow relations in the
   degreewise colimit. Pairing every element of that chain with the common `e` lifts it to
   the pullback diagram, proving injectivity by the quotient equality clause.
6. The degreewise inverses respect simplicial operators and the map over the source. The
   representative formula also proves naturality in the diagram. Thus the comparison is an
   isomorphism for every fixed-universe small diagram, equivalently the pullback functor
   preserves all such colimits.
-/
theorem pullback_preserves_all_small_colimits (B E : SSet.{u}) (p : E ⟶ B) :
    HasColimitsOfSize.{u, u} (Over B) ∧
      HasColimitsOfSize.{u, u} (Over E) ∧
        PreservesColimitsOfSize.{u, u} (Over.pullback p) := by
  sorry

end SSet
