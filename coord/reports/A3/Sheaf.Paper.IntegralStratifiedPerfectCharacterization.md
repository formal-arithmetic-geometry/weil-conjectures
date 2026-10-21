## What changed

Repair of the returned head `24aca3a6142`: removed the redundant file-level
`set_option warn.sorry false`. The hole census tokenized the option component as an
unattributed hole at line 73. The two actual holes in this module remain in named theorems;
no theorem signature, definition, or proof changed in this repair. Compilation succeeds
without the option, and the repaired packet passed server preflight.

Proved `AlgebraicGeometry.Scheme.integralConstantModule_exact` using the existing exact
constant-module sheafification, flat completed scalar extension, and exact coefficient
restriction interfaces. Proved the shift and distinguished-triangle clauses of
`integralStratifiedPerfectClosure` from `pbcIntegralUniformComplete_isTriangulated`.
The truncation and degree-zero cohomology clauses are factored into two strictly smaller
named theorems in new modules and imported by the parent module. The restored auxiliary
coefficient proofs from the quarantined source are retained unchanged.

## Proved and sorry left

Relative to the quarantined source, four original theorem holes become two original
holes plus two new closure lemmas. This is a decomposition with net zero holes closed.
The attribution repair itself closes zero theorem holes and adds zero holes.

Closed or decomposed:

- `AlgebraicGeometry.Scheme.integralConstantModule_exact`.
- `AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure`: shifts and triangles are
  proved; truncation and homology are decomposed into the two new lemmas below.

Preserved existing proofs, not newly closed holes: `integralCoefficientULift_exists`,
  `integralDetailedCoefficientComparison_exists`, and
  `integralDetailedCoefficientRestriction_exact`.

Sorries left:

- `AlgebraicGeometry.Scheme.integralStratifiedPerfectCharacterization` (original node).
- `AlgebraicGeometry.Scheme.integralStratifiedPerfectDetailed` (original node).
- `AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure_truncation` (new node).
- `AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure_homology` (new node).

No definition contains `sorry`.

## No longer needed

None. The exactness proof uses the constant sheaf and completed flatness interfaces, while the
closure proof uses the published uniform-complete triangulated theorem. All other recorded
imports remain needed by the unfinished characterization and detailed comparison statements.

## Where the brief, the DAG or earlier work was wrong

The quarantined source used the obsolete unqualified name `LocallyClosedStratification`; the
current library exposes the required constructible stratification as `Scheme.Stratification`.
The proof also needed an explicit import of `Sheaf.Paper.CompletedConstantAlgebraFlatQuotients`
to access the completed scalar exactness theorem. No target statement was changed.

## New nodes

`lem-weil-pbc-integral-stratified-perfect-closure-truncation` records the standard truncation
clause as a separate theorem for parallel proof. Its node is
`dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-stratified-perfect-closure-truncation.json`.

`lem-weil-pbc-integral-stratified-perfect-closure-homology` records the degree-zero cohomology
clause as a separate theorem for parallel proof. Its node is
`dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-stratified-perfect-closure-homology.json`.

The returned attribution failure came from the option name rather than an anonymous
proof hole. Removing the unnecessary option repairs the source without modifying tools.

The interface correction is recorded in
`coord/changes/A3-integral-stratification-interface.md`.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
