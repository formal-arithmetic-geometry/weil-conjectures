## Worker report

Recorded the existing theorem `IsOpen.topologicalKrullDimAt_eq` in
`WeilConjectures.Mathlib.Topology.KrullDimension`, source lines 341–366. No new Lean
module or proof is delivered. Read its full signature, docstring and proof and both
statement dependencies. It is exactly the node, with no additional assumptions.

Hypothesis and clause correspondence:
- The arbitrary topological space Y is the section variable `{X : Type*}` with
  `[TopologicalSpace X]`; the universe is unrestricted.
- The subset O is `{W : Set X}`, and its openness is `(hW : IsOpen W)`.
- The point y and membership y ∈ O are `{x : X}` and `(hx : x ∈ W)`.
- The subspace topology is the standard `instTopologicalSpaceSubtype` on `W`;
  `(⟨x, hx⟩ : W)` is the same point viewed in the open subset.
- The entire conclusion dim_y(O) = dim_y(Y) is
  `topologicalKrullDimAt (⟨x, hx⟩ : W) = topologicalKrullDimAt x`.

Dependency declarations used:
- `def-kun-topological-dimension-at-point` records `topologicalKrullDimAt` in
  `WeilConjectures.Mathlib.Topology.KrullDimension`. Read lines 327–334: it is the
  infimum of `topologicalKrullDim U` over `U : Opens X` and proofs `x ∈ U`, exactly
  the minimum over open neighbourhoods (the dimension value order is well ordered).
- `def-kun-subspace-topology` is the Mathlib leaf `instTopologicalSpaceSubtype`,
  `Mathlib.Topology.Defs.Induced`, lines 76–78: topology induced by inclusion.

The node's source file is not present in the remote clone's literature directory.
Read the source online: https://stacks.math.columbia.edu/tag/0055, Definition 5.10.1(4),
which defines local dimension by the minimum over open neighbourhoods. The existing
theorem's cofinal-neighbourhood argument matches the node's proof: ambient open sets
restrict to W; open sets of W are ambient open because W is open; inducing inclusions
compare their dimensions and give both inequalities.

Edge cases checked: empty X or empty W has no x with hx, so the quantified assertion
is vacuous; W = X gives the identity under the subtype identification; singleton and
discrete spaces are allowed; infinite dimension is retained in `WithBot ℕ∞`.
There are no Noetherian, separation, sobriety, nonempty-space, or finiteness hypotheses.
No node correction or disputed statement was needed.

Searches performed:
- msearch LeanFinder: "Krull dimension at a point is unchanged on an open subspace";
  returned global-dimension subspace inequalities, no exact Mathlib theorem.
- msearch Loogle: "topologicalKrullDim"; seven results on global dimensions,
  no local-dimension theorem.
- msearch LeanSearch: "Krull dimension at a point of an open subspace";
  service unavailable (Internal Server Error), recorded as unavailable.
- msearch grep: `topologicalKrullDimAt|KrullDim.*(subspace|open)` in Mathlib/Topology;
  only the global-dimension subspace inequality and its module documentation.
- rg of `topologicalKrullDimAt` and the item id in WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found the exact theorem at source line 343 and the
  already recorded dependency definition at source line 333. No duplicate declaration
  was written. Initial rg for `topologicalKrullDimAt|krullDimAt|dimensionAt|dimAt`
  in the plain Topology directories returned no result; the source module is under
  WeilConjectures/Mathlib/Topology. The item id itself has no source occurrence.

Validation: existing-declaration delivery, so no new module requires compilation.
The delivery dry run checks that the recorded declaration exists in its source module.

## Second reading by G1

I independently read the node statement, its source place (Stacks Project topology.tex,
Definition 0055, item (4), and the following remark), and the recorded source declaration.
The node introduces: (1) a topological space Y, rendered by the section variables
`{X : Type*}` and `[TopologicalSpace X]`; (2) a subset O of Y, rendered by
`{W : Set X}`; (3) openness of O, rendered by `(hW : IsOpen W)`; and (4) a point y in O,
rendered by `{x : X}` and `(hx : x ∈ W)`. The subspace topology required by the node is
exactly Mathlib's subtype topology `instTopologicalSpaceSubtype`, so the point in O is
`(⟨x, hx⟩ : W)`. The conclusion `dim_y(O) = dim_y(Y)` is rendered exactly as
`topologicalKrullDimAt (⟨x, hx⟩ : W) = topologicalKrullDimAt x`.

The existing declaration is
`IsOpen.topologicalKrullDimAt_eq {W : Set X} (hW : IsOpen W) {x : X}
(hx : x ∈ W) : topologicalKrullDimAt (⟨x, hx⟩ : W) = topologicalKrullDimAt x`
in `WeilConjectures.Mathlib.Topology.KrullDimension` (source lines 343--366).
Its hypotheses and conclusion match the node clause by clause, with no extra
Noetherian, separation, finiteness, nonemptiness, or universe restriction. The dependency
`topologicalKrullDimAt` is the recorded definition (infimum over open neighbourhoods),
and the subtype topology is the recorded Mathlib declaration. I found no mismatch and
made no mathematical change; I added only the item's `lean` record identifying this
existing declaration.

Edge cases remain covered: an empty ambient space or empty open subset makes the
quantification vacuous; W = X gives the identity; singleton and discrete spaces are
allowed; and `WithBot ℕ∞` retains infinite dimensions. Searches were repeated with
LeanFinder (`Krull dimension at a point is unchanged on an open subspace`), Loogle
(`topologicalKrullDim`), LeanSearch (`Krull dimension at a point of an open subspace`,
service unavailable), and grep over Mathlib and the source repository. They found no
second declaration; the source theorem above is the exact existing match.
