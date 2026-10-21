## What changed

Restored `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal`
from its listed quarantine by re-exporting the complete adopted implementation
in `WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal`.
Both archived public imports are retained. The original fully qualified core
theorem and its complete proof remain available, using the existing definitional
equality `affineTildeFunctor = affinePushforwardTilde`.

Validation: the restored module compiled cleanly with `lcompile.py`, as did
scratch checks of the verbatim archived core signature and the quarantined
consumer's original theorem proof (with fresh local instance names and the
explicit-universe abelian instance used by the adopted implementation).
`#print axioms` for all three reports only `propext`, `Classical.choice`, and
`Quot.sound`. The scratch checks are excluded from the delivered Lean files.

This removes a duplicate local implementation and its stale universe-sensitive
instance/transparency setup. The adopted source and quarantine archive are
untouched. Change record:
`coord/changes/T7-affine-tilde-source-core-final-rework.md`.

## Proved and sorry left

This is a zero-hole quarantine repair: 0 holes closed, 0 holes added, 0 split
off, 0 remaining in the item. The archived public theorem
`AlgebraicGeometry.exists_affineTildeTensorSourceComparisonCore` already had
a complete proof, as did its private helper `normalized_unit_exchange`.
The same public theorem is now supplied by the complete source implementation;
no theorem is replaced by `sorry` and no existential witness is chosen anew.

## No longer needed

No public import, DAG node, dependency, or module is removed or withdrawn.
The restored import path and the dependency of its quarantined parent are kept.
The duplicate instances and private associativity helper are supplied by the
adopted implementation. No new nodes are needed and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned item is a listed quarantine repair, not an unproved theorem.
Its zero-hole count is preserved honestly. The adopted source now proves the
entire archived statement with the same proof, modulo the existing tilde
abbreviation; the historical DIFFERENT twin-retirement note predates the
prerequisite compatibility repairs.

The core helper is documented by
`lem-pc-affine-tilde-tensor-source-comparison`, whose Lean attachment is the
main comparison theorem in a different module. That attachment, its proof
dependencies, and the quarantined parent are preserved. The node's proof plan
is not being replaced, so no node file changes are required.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
