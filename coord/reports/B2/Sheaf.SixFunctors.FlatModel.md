## What changed

Restored Sheaf.SixFunctors.FlatModel from the exact quarantine path in
coord/rework.tsv. Preserved all seven public declarations and the five existing
complete theorem proofs, with the stratification API repairs described in
coord/changes/B2-restore-flat-model.md. The generator predicates and flat-stratification
conclusion now use Scheme.Stratification; the identity partition uses
Stratification.trivial. Added two declaration-local transparency options for proof
elaboration. No source-library or target statement was edited.

The node copy preserves its statement, proof, proof dependencies and attachment;
its restoration note records the migration. The old unit record predates the current
blueprint; the main-20261015 statement and proof were read and their flat-model,
stratification, sheaf-filtration, stupid-tail and comparison route is retained.

Searches through msearch.py used Loogle (DerivedCategory/flat: no results), LeanFinder
(bounded constructible finite-Tor models and generation: bounded representatives only),
and grep (hasTorAmplitudeIn_iff_exists/ctf_generated_by_rightDerived: no service hits).
Direct source inspection found the existing upstream flat-model and generation theorems;
the existing proof already uses the finite-value model and comparison inputs needed
for these intrinsic coefficient statements. No new lemma or proof route was introduced.

Validation: deliver3.py compiled the repaired module with its axiom probe and
passed its independent server single-file compilation, without warnings. During
the initial diagnostic compiles, the published FlatModelGeneration artifact still
used the retired type; its restored source became available to the compiler during
the delivery run. No dependency was copied, changed or rebuilt by this worker to
work around publication. No diagnostic Lean module is included in the packet.

## Proved and sorry left

Restoration/API repair: 0 of 0 archived sorries closed, 0 added, 0 split off.
There are no direct sorry declarations in the item. The five already-complete proofs
are preserved, not claimed as newly proved: AlgebraicGeometry.proEtaleFlatModel,
AlgebraicGeometry.proEtaleFlatStratification, AlgebraicGeometry.etaleThickGeneration,
AlgebraicGeometry.proEtaleThickGeneration, and AlgebraicGeometry.proEtaleThickGeneration_eq.
The delivery does not modify or claim to close any imported dependency's holes.

## No longer needed

Removed only the empty, retired public import
Sheaf.AlgebraicGeometry.LocallyClosedStratification. Its role is supplied by the existing
canonical Scheme.Stratification API. No node, mathematical dependency, declaration or
module is withdrawn. In particular FlatModelGeneration remains required for its etale
ordered-stratification, filtration and thick-generation clauses. The quarantine archive
and both quarantined consumers remain intact.

## Where the brief, the DAG or earlier work was wrong

The active item was absent following the cluster restoration; this is a rework repair,
not evidence that its mathematics was withdrawn. Its archive uses the retired
stratification type and identity constructor. The current source migration is documented
by A4's FlatModelGeneration restoration. The initial compile snapshot still contained
an older artifact of that dependency with references to the removed type. The normal
publication caught up during the delivery run. No other group's dependency was altered
or rebuilt and the mathematical route was retained.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
