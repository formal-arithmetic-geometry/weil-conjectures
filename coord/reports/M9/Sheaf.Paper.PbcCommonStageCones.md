## What changed

Proved `AlgebraicGeometry.Scheme.qbarStagePretriangulated_exists` in
`Sheaf.Paper.PbcCommonStageCones`, with every existing signature unchanged.
The proof compares the tensor-Hom scalar localization with the existing Verdier
rationalization via `Rationalization.tensorHomEquiv`, transfers its localization
property, and applies Mathlib's `Triangulated.Localization.pretriangulated` with
the already published PBC shift and rationalization comparison. A proved private
extensionality lemma gives uniqueness from equality of distinguished-triangle sets.
The concrete chosen instance and common-stage distinguished predicate are unchanged.
Updated the node's proof, proof dependencies and proof origin to follow this argument.

Validation: the retained module compiled cleanly through `lcompile.py` on
2026-10-19 in 5.9 seconds, against the current published library. The required
stage-3 delivery preflight is also run before delivery. No target, public signature
or definition changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.qbarStagePretriangulated_exists`
(node `def-weil-pbc-common-stage-cones`).
No `sorry` remains in the delivered module. No holes or split-off theorems added.
The integral triangulation and normalized shift declarations remain existing proof
dependencies; this delivery does not claim to close their holes.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`
(node `lem-weil-linear-scalar-localization-triangulated`): its existentially chosen
shift would require an additional comparison with the published PBC shift.
Using the existing rationalization Hom equivalence and Mathlib localization
construction directly works with that published shift and avoids this transport.
Also removed the redundant proof import
`Mathlib.CategoryTheory.Triangulated.Triangulated`; the rationalization and
localization imports already provide it.
The scalar-localization category operations, integral triangulation and common-stage
calculus are still used. All public imports are retained because the statement,
chosen instance and distinguished predicate use their structures.
No unit statement or unit proof step is bypassed; the assigned node realizes none
of the unit's retained statement/steps. No other modules are withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned file was briefly absent from the shared tree during initial reads,
then became available unchanged before it was copied into the sandbox.
The original existence proof plan unnecessarily reconstructs and identifies the
rational shift. Mathlib's localization constructor accepts the existing shift and
CommShift directly once the localization universal property is supplied.
No mathematical statement or definition repair is needed.
The retained change record's earlier claim of no direct consumers was stale:
the resumed consumer check finds ten. They require no adaptations because the
public interface and definitions are unchanged. The change record is
`coord/changes/PbcCommonStageCones.md`.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
