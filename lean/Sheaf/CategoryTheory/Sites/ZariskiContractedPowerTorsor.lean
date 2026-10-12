/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.Sites.CoherentContractedPowers
import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Existence of coherent contracted powers of a torsor

Source: blueprint `sec-curve-estimates/sk-prop-hilbert90/lem-sc-torsor-h1.md`,
contracted-product group law (blueprint: lem-sc-zariski-contracted-power-torsor).
-/

@[expose] public section

universe uCT wCT

open CategoryTheory TopologicalSpace

namespace CategoryTheory.Sheaf.Torsor

/-- Every Zariski torsor under an abelian sheaf has coherent integer contracted powers.
Source: blueprint `lem-sc-torsor-h1`, worker's coherent integer-power construction.

Proof: (1) Choose local sections `t₀`. Positive factors have coordinates `a` with
`t = a +ᵥ t₀`; inverse factors use the negated action. The antidiagonal relation changes
`(a,b)` to `(a+g,b-g)`, preserving the sum. Iterated sheaf quotients are therefore locally
translation torsors; degree zero is `G` (def-sc-gm-torsor, lem-sc-torsor-h1).
(2) Define the quotient maps by addition of local coordinates. Under `t₁ = c +ᵥ t₀`,
a degree `k` coordinate changes by `-kc`, so the source and target change equally.
Thus the maps glue and identify the contracted products with the sum-degree powers.
Degree one is `T`, and the degree-zero maps are the original actions
(def-sc-gm-torsor, lem-sc-torsor-h1).
(3) On a trivializing open the two associative composites are `a+b+d`, the swap is
`b+a=a+b`, and the unit formulas are addition by the degree-zero coordinate. These
identities descend to the sheaf quotients (lem-sc-torsor-h1).
(4) For `t = a +ᵥ t₀` and `s = (-b) +ᵥ t₀`, the unique `h` with `h +ᵥ s = t` is
`a+b`. It is invariant under the antidiagonal relation. Conversely its class is locally
`[h +ᵥ s,s]`, independently of the choice of `s`. This is the cancellation pairing;
the same construction works in degrees `n,-n` (def-sc-gm-torsor, lem-sc-torsor-h1).
(blueprint: lem-sc-zariski-contracted-power-torsor) -/
theorem nonempty_coherentContractedPowers (X : AlgebraicGeometry.Scheme.{uCT})
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{wCT}) (T : Torsor G) :
    Nonempty (CoherentContractedPowers X T) := by
  sorry

end CategoryTheory.Sheaf.Torsor
