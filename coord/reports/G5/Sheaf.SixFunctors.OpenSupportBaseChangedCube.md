## What changed

Proved `AlgebraicGeometry.Etale.openSupportBaseChanged_cube` with its original signature.
The proof factors the specified comparison into a graph comparison and a proper/open and
open-composition tail. It constructs the map between the two iterated pullback ambients,
proves its factor squares Cartesian, and pastes the factor equations by naturality.
Cancelling the invertible compact-support exchanges gives the original equation.

Added three modules under `Sheaf.SixFunctors`:

- `OpenSupportFactorModel` constructs `openSupportTailIso` as a concrete composite of
  the existing proper/open and open-composition isomorphisms.
- `OpenSupportGraphExchange` proves Cartesian exchange of a single graph comparison.
  It reuses the existing single-graph base-change and identity-normalization equations.
- `OpenSupportTailCube` proves the tail equation from the existing proper/open cube and
  unit-normalized open exchange pasting. Private proved helpers handle the open word,
  naturality and conjugation from exact to left derived inverse image.

The new proof dependencies are private imports. Proof-only `import all` reuses the existing
private normalization helpers without modifying their source modules. The general raw
exchange for supplied Cartesian representatives is reused from
`rightDerivedLowerShriekOfCompactificationBaseChangeMap'`; no duplicate is defined.
No existing definition, declaration signature or public import changes. No consumer
adaptations or change records are needed.

Final server compilation passed without warnings for all four files: factor model 29.4 s,
graph exchange 27.2 s, tail cube 50.4 s, assigned cube 49.0 s. Each is below 60 s.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.openSupportBaseChanged_cube`
(node `lem-asd-open-support-base-changed-cube`).

The two new factor theorems are also proved:
`AlgebraicGeometry.Etale.openRestrictionGraphIso_cartesianExchange`
(node `lem-asd-open-support-graph-exchange`) and
`AlgebraicGeometry.Etale.openSupportTail_cube`
(node `lem-asd-open-support-tail-cube`). All private helpers are proved.

Original holes closed: 1 of 1. Holes added: 0. Holes remaining in the four delivered Lean
modules: 0. No obligation is split off with sorry. Existing lower library declarations are
used as allowed in stage 3; this does not claim the whole targets' dependency closure is
already axiom-free. The new definition is a concrete composite, not an existence witness.

## No longer needed

No original import is removed, no module is withdrawn, and no module is claimed globally
pruned. The new factor and graph modules import `OpenRestrictionCompactSupport` directly;
they do not import `OpenSupportCompactificationModel`. The latter remains needed by the
item and tail statements for the specified invertible compactification exchange.

The five broad dependencies of the original plan are no longer direct proof dependencies
of this node: `lem-etale-unbounded-compact-support-composition`,
`lem-kun-proper-base-change-torsion-ring`, `lem-cbc-extension-zero-base-change`,
`lem-cbc-extension-zero-composition`, and `lem-weil-pbc-mate-pasting`. The actual route is
recorded through the concrete factor, graph exchange and tail cube nodes. Graph composition,
proper exchange, open base change and open composition still occur below these factors;
this is not a claim to prune those lower results globally. The general mate-pasting node
has no Lean attachment, so its intended calculation is performed using the existing
single-graph/exact-exchange helpers and explicit naturality equations.

## Where the brief, the DAG or earlier work was wrong

The original mate-pasting dependency has `lean: null`, despite the brief's general
statement that proof dependencies have Lean declarations. Existing graph-exchange helpers
supply the needed calculation, so this does not block the proof.

The public graph-compositor base-change theorem assumes quasi-compact output morphisms.
It cannot prove this unrestricted statement directly. The proof instead uses the existing
single-graph theorem for arbitrary Cartesian representatives, with no added hypotheses.

The unit `sk-prop-sf-cbc` has no realized statement or proof steps to bypass. The argument
follows the blueprint's coherence (i), handling its graph, proper/open and open factors.
Empty schemes, empty opens, identity base changes and the zero ring require no extra
hypotheses: all calculations use naturality, pullbacks and specified isomorphisms.

Two local-mirror checks failed before elaboration because published dependency artifacts
were missing (`BaseChange.Square.olean`, then `RingObjects.Ab.olean`). Later checks use the
wrapper's documented server-only option. No launcher tool or published library was changed.

## New nodes

Blueprint-wide searches for `open support`, `graph comparison` and `proper/open` found no
separate statement of these factor identities. The broader results are used below them.

`def-asd-open-support-factors` records the concrete tail `openSupportTailIso` in
`OpenSupportFactorModel`.

`lem-asd-open-support-graph-exchange` records the proved Cartesian exchange of a single
graph comparison in `OpenSupportGraphExchange`.

`lem-asd-open-support-tail-cube` records the proved proper/open and open-compositor
calculation in `OpenSupportTailCube`. Its proof includes the exact-inverse-image calculation
and the explicit transport to left derived inverse image. No new node contains a hole.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
