## What changed

Completed `AlgebraicGeometry.nagataQCOpenDescent_spec` in
`Sheaf.AlgebraicGeometry.NagataQCOpenDescentSpec`, preserving its full signature.
The proof unfolds the selected finite-stage construction, proves compactness of its
finite union of affine basic opens, and identifies the inverse image of every basic
open using `Scheme.basicOpen_appLE`, the cone equation, and `hlift`. It then uses the
presentations and cover equation to recover `W`. The DAG proof and proof dependencies
now describe this argument. No definitions, statements, or public imports changed.
The completed file compiled cleanly on the project server in 4.5 seconds.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.nagataQCOpenDescent_spec`
(node `lemma-nagata-qc-open-descends`).
Holes closed: 1. Holes added: 0. Sorries left in the delivered module: none.
No split-offs and no new modules. The existing declarations used to construct the
selected stage and chart restrictions retain their pre-existing proofs; this delivery
does not claim to close their holes.

## No longer needed

The proof does not need `lem-weil-pbc-limit-global-sections-colimit`
(`AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone` and the elementwise representative
lemmas in `Mathlib.AlgebraicGeometry.AffineTransitionLimit`). The chosen sections and
their exact pullback equations are already supplied as `lift` and `hlift`, so no
existence or colimit argument is required for this specification theorem. Removed
that node from `proof_deps` and removed its two obsolete `tool_uses` entries. It may
remain needed elsewhere, in particular for producing the input lifts.

No other planned dependency is pruned: the descent construction, directed finite
upper-bound property, and basic-open pullback fact are all used. No module is
withdrawn and no proof import is removed.

## Where the brief, the DAG or earlier work was wrong

The old proof plan repeats the global-sections colimit argument after the Lean
statement has already supplied its outcome as `hlift`. The current proof uses that
hypothesis directly. This is a node-level simplification and retains the unit's
finite-stage chart/lift route. No mathematical statement was changed or disputed.
The empty-cover case and empty basic-open presentations are handled by the same
supremum identities, without extra hypotheses.

Searches were run with the required `msearch.py` LeanFinder, Loogle, and grep
interfaces. They identify `Scheme.basicOpen_appLE` and
`Scheme.preimage_basicOpen`; the exact custom selected-stage specification is absent
from the source-library searches. No new statement was introduced.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
