## What changed

Restored `Sheaf.Paper.WeilTensorProduct` from its quarantine archive and repaired
elaboration of `AlgebraicGeometry.Scheme.wfTensorRepresentative_exists`.
The original fails with four stuck universe constraints of the form
`u + 1 =?= max (u + 1) ?u`, followed by the missing representative theorem.
The repair uses command-scoped instance exclusions for
`CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall` and
`WeilConjectures.integralOperationsSiteSmall`. The existing fixed-universe
instances remain available; the exclusion ends after this theorem command.

All existing declaration signatures, proof bodies, definitions, attributes and
imports remain verbatim. Only the scoped elaboration command is added.
The complete module compiled without warnings or errors in 52.4 seconds.
The change record is
`coord/changes/B7-weil-tensor-representative-universes.md`.

The attachment and mathematical proof route of `def-wf-tensor-product` are
preserved. No DAG change is needed: this is an instance-inference repair.
No consumer adaptation is necessary. The sole direct reference to the theorem
is `wfTensorModel` in the same module, checked in the complete compile. No target
statement, definition data, or target interpretation changes.

## Proved and sorry left

This is a listed compilation repair with zero initial holes. Closed 0 of 0
sorries; added 0; split off 0. No declaration in the restored module contains
`sorry`. In particular, `AlgebraicGeometry.Scheme.wfTensorRepresentative_exists`
retains its complete proof from the existing library declarations.
The full delivery probe checks all declarations and their axioms.

## No longer needed

None. No import, module, declaration or node dependency is removed.
Quarantined parents and their mathematical dependencies remain preserved.
No unit statement or proof step is bypassed. The archive is not deleted.

## Where the brief, the DAG or earlier work was wrong

The module is absent from `lean/` because it was quarantined, as recorded in
`coord/rework.tsv`; its absence does not indicate withdrawal. The archive has
zero holes. Its failure is an instance-inference conflict during the theorem's
statement elaboration, reproduced even with the theorem proof omitted in a
scratch file. Explicit universes on tensor-comparison and localization terms
alone did not fix it. The scoped instance exclusions preserve the existing
statement and proof and allow the original construction to compile.
Server busy responses were retried until actual compiler results were obtained.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
