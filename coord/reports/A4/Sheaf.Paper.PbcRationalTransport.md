## What changed

Restored `lean/Sheaf/Paper/PbcRationalTransport.lean` verbatim from
`quarantine/Sheaf/Paper/PbcRationalTransport.lean`, as assigned by the current
`coord/rework.tsv` row. The module was absent after the cluster restore; this delivery
restores its complete public interface and proofs rather than withdrawing it.

The restored module compiles through `lcompile.py` with exit code 0 in 31 seconds.
Its scalar extension uses actual tensor maps. Exactness specializes the existing
`SemilinearScalarLocalization.extension_exact` to the identity coefficient map;
uniqueness and exchange use tensor induction and natural-transformation extensionality.
The existing node `prop-weil-pbc-rational-transport` already records this exact proof
route, all Lean attachments, and the semilinear dependency, so it requires no edit.

No signature, definition, instance, visibility, import, or proof differs from the
quarantined source. Consequently no consumer adaptation or new interface change record
is needed. The original proof-import change record is
`coord/changes/pbc-rational-transport-proof-imports.md`.
There are no active direct importers; the 25 quarantined direct importers retain exactly
the archived interface, including `PbcScalarExtension`, `PbcCohomologySheaves`,
`PbcDescentFunctors`, `RationalOperations`, and `RationalVerdier`.

## Proved and sorry left

This is a restoration with zero original holes, zero holes closed, zero holes added,
and zero holes left in the restored module. No statement is split off.
The archived complete proofs of `CategoryTheory.ScalarLocalization.transport_exact`,
`WeilConjectures.pbcRationalTransport`, and `WeilConjectures.pbcRationalExchange`,
and all their tensor-law, uniqueness, and naturality helpers, are preserved.
Dependencies may still have their own named proof obligations; this restoration does
not claim to close them or to establish the final target axiom criterion.

## No longer needed

None. No imports, declarations, nodes, or modules are removed. The quarantined source
and its DAG attachment and dependencies are preserved. The unit route is unchanged.
Fresh LeanFinder, Loogle, and Mathlib grep searches confirmed that the general categorical
localization lemmas require additional localization identifications; they do not replace
the existing direct tensor construction more simply.

## Where the brief, the DAG or earlier work was wrong

The assigned module currently has no `sorry`: the rework is restoration of an absent
module after the cluster restore, rather than filling a new proof hole. Its archived
complete proof already works against the current compiled dependencies. No mathematical
error, false statement, or mismatch between the existing DAG proof and Lean was found.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
