## What changed

Restored `lean/Sheaf/Paper/CondensedPointCoefficients.lean` byte for byte from its
quarantine archive. The assigned rework row records a cluster-restore rollback;
its live absence is a source defect. All four constructions and the theorem
`AlgebraicGeometry.ProEtale.condensed_point_coefficients` are restored with their
complete proofs and original imports. No consumers require adaptation.

The restored file compiles without diagnostics in 8.9 seconds. A temporary axiom
probe compiled in 5.8 seconds: all five public declarations use only `propext`,
`Classical.choice` and `Quot.sound`; the probe is excluded from the delivery.
The declaration and import searches find no current Lean consumers. The original
DAG attachment, dependencies and geometric-point unit route are preserved.

Change record: `coord/changes/B6-restore-condensed-point-coefficients.md`.

## Proved and sorry left

Original archived holes: zero. Holes closed: zero. Holes added: zero. Split off:
zero. Remaining holes: zero. The restored theorem
`AlgebraicGeometry.ProEtale.condensed_point_coefficients` and its three private
proof helpers are already fully proved (node `det-pe-condensed-point-coefficients`).
This delivery repairs missing source; it does not claim a newly closed hole.

## No longer needed

None. No import, declaration, module or DAG dependency is removed. The archived
proof already follows the recorded dense-subsite, monoidal-adjunction,
finite-quotient-colimit and discrete-constant-comparison route. Searches found
Mathlib's locally constant colimit lemmas but no replacement for the entire
geometric-point coefficient theorem. The existing complete proof is retained.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an item with proof holes; this particular item is
instead a quarantined-source restoration with zero holes, as allowed by the
repair instructions. The archive is the authoritative source. No mathematical
statement, definition or proof-plan error was found. The previously restored
discrete-constant comparison is available and the archived proof compiles against
it. No new nodes are needed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
