/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exactness of closed-subset pushforward for abelian sheaves

Source: Stacks Project, Sheaves of Modules, Lemma 17.6.1 (Tag 01AX), exactness assertion
(blueprint: lem-sc-closed-immersion-pushforward-exact).
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

/-- Pushforward along the inclusion of a closed subset preserves short exact sequences
of abelian sheaves. The existing `pushforward` evaluates on an open `U` by evaluating
on its inverse image in `Z`, namely `U ∩ Z` with the subspace topology.
Source: Stacks Project, Sheaves of Modules, Lemma 17.6.1 (Tag 01AX), exactness assertion
(blueprint: lem-sc-closed-immersion-pushforward-exact).

Proof:
1. For a short exact sequence on `Z`, the on-image stalk description identifies its
pushed-forward stalk sequence at each `z ∈ Z` with the original stalk sequence, including
both maps (lem-sc-closed-pushforward-abelian-stalks).
2. Off `Z`, all three pushed-forward stalks are zero by the same stalk description, so
that sequence is short exact. On `Z`, stalkwise detection applied to the original short
exact sequence shows that its stalk sequence is short exact
(lem-sc-abelian-sheaf-short-exact-stalkwise).
3. Stalkwise detection on `X` now makes the pushed-forward sequence short exact
(lem-sc-abelian-sheaf-short-exact-stalkwise). The original sequence was arbitrary. -/
theorem shortExact_map_pushforward_closedSubset
    (X : TopCat.{u}) (Z : Set X) (hZ : IsClosed Z)
    (S : ShortComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}))
    (hS : S.ShortExact) :
    (S.map (pushforward AddCommGrpCat.{u}
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X))).ShortExact := by
  sorry

end TopCat.Sheaf
