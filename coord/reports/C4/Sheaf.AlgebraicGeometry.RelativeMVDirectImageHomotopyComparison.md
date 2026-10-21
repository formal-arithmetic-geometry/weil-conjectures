## What changed

Restored the assigned module
`lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageHomotopyComparison.lean`
from its quarantine path, byte-for-byte. Its public statement, universe parameters,
visibility, docstrings, public imports, private proof import and two private
proved helpers are preserved. The existing node's Lean attachment and proof
plan match the restoration exactly; no node update or new node is necessary.
No other module or definition changes.

The proof obtains resolved short exact rows from
`AlgebraicGeometry.relativeMV_direct_image_rows`, identifies their cones with
the quotient vertices by Mathlib's `quasiIso_descShortComplex`, and transports
cone/quotient naturality through localization and the pinned adjunction.
The quotient mate equation proves the overlap identity. Global and middle
identities come directly from the row theorem.

Change record:
`coord/changes/C4-relative-mv-direct-image-homotopy-restoration.md`.

## Proved and sorry left

Restoration of an already proved quarantined module: 0 of 0 holes closed,
0 holes added, 0 split off, 0 remaining.
`AlgebraicGeometry.relativeMV_direct_image_homotopy_comparison` and the private
helpers `cone_quotient_naturality` and `cone_mate_quotient` have complete proofs.
There are no remaining declarations with `sorry` in this delivery.

The byte-identical restored module compiled cleanly with `lcompile.py` against
the published server build in 20.2 seconds. A source check confirms the public
signature is exactly the node's `lean.statement`, all Lean lines are at most
100 characters, and no forbidden declaration or hole is present.

A separate validation set compiled this exact source with an appended
`#print axioms` in 26.2 seconds and its unchanged archived direct consumer
`Sheaf.AlgebraicGeometry.RelativeMVCoverChainSquare` in 24.7 seconds.
Both final public declarations depend only on `propext`, `Classical.choice`
and `Quot.sound`. The validation copies and diagnostic commands are outside
the delivery's `lean/` tree and are not delivered.

## No longer needed

None. No import, node, module or declaration is pruned or withdrawn.
All existing dependencies are used by the restored proof or its statement.
Loogle confirms `CochainComplex.mappingCone.map_descShortComplex`; LeanFinder
returns the additive cone comparisons; Mathlib source searches confirm
`mapHomologicalComplexIso_hom_descShortComplex`, `quasiIso_descShortComplex`
and the adjunction naturality lemmas used here. There is no duplicate existing
relative comparison that would remove the resolved-row step.

## Where the brief, the DAG or earlier work was wrong

The item is a missing-source rework, not an unproved declaration: the quarantine
archive already contains a complete proof with zero holes. The archive remains
needed by the quarantined parent `RelativeMVCoverChainSquare` and its DAG plan.
Restoring it compiles against the current row theorem and source-library imports,
so no statement repair, additional lemma or forced consumer adaptation is needed.
The unit route and adopted source library are preserved.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
