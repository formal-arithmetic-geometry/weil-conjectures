/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Flasque
import Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective

/-!
# Flasque sheaves are acyclic

Source: literature/stacks-project/cohomology.tex, Lemma Tag 09SY (lemma-flasque-acyclic)
(blueprint: lem-sc-zariski-flasque-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

/-- A flasque abelian sheaf on a topological space `X` has vanishing cohomology
`H^q(X, F) = Sheaf.H' F q ⊤` in every positive degree `q`.
Source: Stacks Project, `cohomology.tex`, Tag 09SY (`lemma-flasque-acyclic`)
(blueprint: lem-sc-zariski-flasque-acyclic).

Proof:
1. Let `0 → F → I → Q → 0` be short exact with `I` injective. Abelian sheaves are the
   modules over the locally constant sheaf `ℤ_X`, so `I` is an injective `ℤ_X`-module and
   its restrictions are surjective (`lem-sc-ringed-space-injective-restriction-surjective`):
   `I` is flasque (`def-sc-zariski-flasque`). As `F` is flasque, `I(V) → Q(V)` is surjective
   for every open `V`, and `Q` is flasque (`lem-sc-zariski-flasque-quotient-sections`).
2. Embedding into injectives (`lem-weil-pbc-site-sheaves-enough-injectives`) and iterating on
   the flasque quotients gives an injective resolution `F → I^•` whose complex of sections
   `I^•(V)` is exact in positive degrees for every open `V`.
3. By `def-sc-zariski-cohomology`, `H^q(X, F)` is the `q`-th cohomology of `I^•(X)`, which
   vanishes for `q > 0` by step 2. -/
theorem IsFlasque.subsingleton_H'_top {X : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] (q : ℕ) (hq : 0 < q) :
    Subsingleton (CategoryTheory.Sheaf.H' F q ⊤) := by
  sorry

end TopCat.Sheaf
