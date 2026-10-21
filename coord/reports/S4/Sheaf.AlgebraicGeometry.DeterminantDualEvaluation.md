## What changed

Retired Sheaf.AlgebraicGeometry.DeterminantDualEvaluation in favor of the fully
proved adopted WeilConjectures.AlgebraicGeometry.DeterminantDualEvaluation.
Its sole consumer, Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation,
privately imports the adopted theorem and ExteriorSheafPowerComparison.
It precomposes the adopted ordinary evaluation with the tensor of the two
exteriorSheafPowerIso comparisons, keeping the exact legacy determinant objects
in its public statement and the existing derived proof unchanged.

The ordinary DAG node now attaches to the adopted theorem and records its
canonical exteriorPower proof; the shifted node records the comparison transport.
No source-library declaration, target, public consumer import or signature changes.
Change record: coord/changes/S4-retire-determinant-dual-evaluation.md.
The adapted consumer compiles cleanly through lcompile.py (23.4 seconds).
Its public theorem signature, public imports, and private helpers were checked
verbatim against the original; all are unchanged.

## Proved and sorry left

The item has zero initial holes and zero remaining holes. No hole is closed or
added: AlgebraicGeometry.determinant_dual_evaluation was already proved and is
now provided by the adopted theorem. AlgebraicGeometry.shiftedDeterminant_dual_evaluation
and all its private helpers remain fully proved. No new modules or statements
are split off. This delivery is a duplicate retirement, not a new theorem proof.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.DeterminantDualEvaluation.
Removed its only consumer import, replacing it with the adopted module.
No DAG node is deleted or detached: lem-sc-determinant-dual-evaluation remains
attached to the adopted theorem. The ordinary node no longer needs
lem-sc-exterior-sheaf-power-comparison internally; its consumer now uses that
comparison explicitly. Other determinant dependencies remain needed by the
adopted proof. No additional module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open hole, but the current item has zero
holes and is a listed retirement item (coord/retire-items.tsv:1789).
The historical PROOFDIFF_UNSAFE blocker no longer applies: its determinant
and dual-pairing prerequisites have been retired. The new consumer import
closure contains no active pair of Sheaf/upstream twin modules. The two
exterior constructions have different Lean types, so the consumer needs the
existing comparison isomorphisms rather than an import-only rewrite.
The unit route is unchanged, including ordinary evaluation and the derived
single-complex and cancelling-shift steps.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
