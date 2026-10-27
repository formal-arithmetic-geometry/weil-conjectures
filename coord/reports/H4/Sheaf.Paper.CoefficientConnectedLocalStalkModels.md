## What changed

Completed the Lean proof of
`AlgebraicGeometry.Scheme.coefficient_connected_local_stalk_models` without changing its
statement or public imports. The proof privately imports the new chart-atlas module,
Mathlib's site-equivalence API, and the scheme pullback-carrier API.

The proved private helper `stalks_agree_on_component` shows that the isomorphism class
of a stalk is constant on a connected component when it has an open cover of constant
models. Both the class and its complement are open. The main proof constructs the
etale pullback charts over the test object, proves their joint surjectivity, transports
the generated covering sieve through AsSmall, and composes the stalk and chart model
isomorphisms on every arrow of that sieve. This includes the empty-object case.

The remaining local finite-model/stalk/comparison transport is isolated in
`Sheaf.Paper.CoefficientEtaleDerivedChartAtlas`. Its theorem permits different charts
to have different algebraic models. The final compile of both files passed cleanly: 8.9 seconds for the atlas and
11.7 seconds for the main module. The original theorem signature is textually identical.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.coefficient_connected_local_stalk_models`
(node `lem-sfb-coefficient-connected-local-stalk-models`). The assigned module has
zero remaining holes and its private topological helper is proved.

Added one hole:
`AlgebraicGeometry.Scheme.coefficient_etale_derived_chart_atlas`
(node `lem-sfb-coefficient-etale-derived-chart-atlas`), in its own new module. This is
an explicit public theorem with proof exactly `by sorry`, a source and complete proof
in words. No definition or private declaration contains a hole.

This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
It is not a claim that the target is now independent of sorry. The open/complement
connectedness argument and the geometric covering-sieve construction are actual Lean
proofs, rather than further assumptions.

## No longer needed

No original public import is removed, and no existing module is withdrawn.

The old dependency `lem-sfb-noetherian-connected-components-open`
(`WeilConjectures.Mathlib.Topology.NoetherianSpace`) is unnecessary on this route.
There is no factorization through an open connected component: the topological helper
works for every topological space and the covering charts are pulled directly to U.
The original Noetherian-scheme hypothesis remains unchanged in the assigned signature.

The old dependency `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
(`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`) is also unnecessary for
this route. The chart transport needs exact inverse image commuting with constants,
not the general monoidal derived tensor comparison. The new atlas plan instead uses
the existing fixed-scalar comparison API and the constant realization API.

The bounded constant-model, exact stalk, constant stalk, geometric-point lifting,
constant-scalar, and weakly etale localization dependencies remain needed in the
new atlas node. They have moved below the local chart step and are not claimed pruned.
The Mathlib etale-to-pro-etale cover node is now recorded explicitly for the proved
covering-family argument.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed and no target or shared definition is changed. The original
plan's openness of connected components is stronger than needed; the implemented
argument proves directly that the relevant stalk-isomorphism class is both open and
closed. Empty U is handled by the empty covering family without any separate theorem
asserting triviality of its slice category.

The existing `exists_site_bounded_constant_model` theorem already proves the abstract
finite local-model construction. The unfinished work is transporting that result from
fixed-module sheaves to the literal coefficient-sized intrinsic-module, specified
geometric-stalk and comparison-restriction functors. Searches did not find this whole
transport assembly already stated. Its proof plan uses the existing declarations,
not an assertion that their own holes prevent their use. An attempted direct assembly
encountered universe/derived-instance inference problems in the fixed-scalar slice
categories; the compiled reduction isolates that work while retaining the completed
connectedness and geometric-cover arguments.

## New nodes

`lem-sfb-coefficient-etale-derived-chart-atlas`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-coefficient-etale-derived-chart-atlas.json`,
is realized by the new module `Sheaf.Paper.CoefficientEtaleDerivedChartAtlas`.
It is the individual-chart part of Stacks 094G/09BI with exact stalk and comparison
transport. It has no chosen base point z, connected-component hypothesis, test object U,
or covering-sieve conclusion. It gives varying local algebraic models, not a single
specified stalk model. The parent supplies the missing connectedness argument and
constructs the required sieve in Lean, so this is a strictly smaller step rather than
the parent obligation under another name. The blueprint unit and its route are retained.
For edge cases, empty X gives the empty chart family, zero complexes have zero models,
reversed bounds are replaced by a lower min(c,d), and no Tor-amplitude assumption is
introduced. No change record is needed: only the assigned module/node and the new
module/node are changed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
