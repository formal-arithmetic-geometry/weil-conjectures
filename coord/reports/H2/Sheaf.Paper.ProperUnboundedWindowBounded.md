## What changed

Restored `lean/Sheaf/Paper/ProperUnboundedWindowBounded.lean` from the quarantine path
specified by `coord/rework.tsv`. The module had been removed by the merge queue after a
cluster restore. Its archived proofs already compile against the current dependencies;
this delivery restores the complete module, including both declarations, all public
imports, and both proof-only imports. The existing DAG attachment and proof route are
preserved without modification.

For each coefficient ring the proof obtains a common lower cohomology bound from
`hbound`, applies `CondensedRing.condensed_boundedBelow_preservesCoproduct`, and exhibits
the image of the source coproduct as the target coproduct. The canonical comparison is
then the identity by the colimit universal property. This includes an empty indexing
type and equal or reversed bounds. The unit's bounded-family step remains available.

Validation: `lcompile.py` accepted the restored module with exit code 0, no errors or
warnings (9.1 seconds). Read the signatures of all five recorded proof dependencies.
LeanFinder, Loogle, and Mathlib grep searches found no shorter replacement for the
existing library specialization. No definition or statement changed; no consumer
adaptation or change record is required.

## Proved and sorry left

This is a zero-hole restoration, not a new proof or decomposition. The archived module
already had zero holes. Restored the complete proofs of:

- `AlgebraicGeometry.ProEtale.properUnboundedWindowBounded`.
- `AlgebraicGeometry.ProEtale.properUnboundedWindowBounded_padicAlgCl`.

Both realize `det-proper-unbounded-window-ii-bounded`. Holes closed in this session: 0
of 0. Holes left: 0. Holes added: 0. Split-off statements: 0. No new assertion about
the axiom closure of existing dependencies is made.

## No longer needed

None newly pruned. Every import of the archived module is preserved. Its existing
short route uses the bounded-below coproduct theorem rather than a fresh truncation
induction; the existing node already records that route. No module is withdrawn and
no quarantined parent or dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving holes, but this rework item is an absent module
whose quarantined source already contains two complete proofs. Restoration, with the
actual hole count zero, is the needed repair. There is no current H2 return requiring
a different mathematical repair. The node and its Lean attachment remain valid.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
