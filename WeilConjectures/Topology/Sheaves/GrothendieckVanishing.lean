/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import WeilConjectures.Topology.Sheaves.NoetherianColimit

/-!
# Grothendieck vanishing

Let `X` be a noetherian topological space of dimension `d` in which every irreducible closed
subset has a generic point (for instance the underlying space of a noetherian scheme). Then
`Hᵠ(X, F) = 0` for every abelian sheaf `F` on `X` and every `q > d`
(`TopCat.Sheaf.subsingleton_H_of_topologicalKrullDim_lt`, blueprint
`lem-sc-zariski-dimension-bound`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- Blueprint `lem-sc-zariski-dimension-bound`: The Zariski dimension bound (Grothendieck
vanishing).

Let `X` be a noetherian topological space of dimension at most `d`, in which every irreducible
closed subset has a generic point. Then `Hᵠ(X, F) = 0` for every abelian sheaf `F` on `X` and
every `q > d`. The blueprint states this for the underlying space of a noetherian scheme, which
is quasi-sober (`AlgebraicGeometry.Scheme.subsingleton_H_of_topologicalKrullDim_lt`). -/
@[stacks 02UZ]
theorem subsingleton_H_of_topologicalKrullDim_lt [NoetherianSpace X] [QuasiSober X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {q : ℕ}
    (hq : topologicalKrullDim X < q) : Subsingleton (Sheaf.H F q) :=
  sorry

end TopCat.Sheaf
