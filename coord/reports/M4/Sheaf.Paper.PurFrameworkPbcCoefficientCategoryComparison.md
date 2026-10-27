## What changed

Reduced `WeilConjectures.purFrameworkPbcCoefficientCategoryComparison` by constructing
the finite stages from `fdIntegralIdentityRationalEquivalence`, retaining their inverse
formulas, and assembling the specified scalar data with
`fdCompletionInverseScalarCoherence` and `fdNormalizedCommonStageDescent`.
The finite-field linearity step is isolated as the strictly smaller theorem
`fdCompletionFiniteStageLinear`, with the tensor proof documented in its module and node.
`fdHomLinearEquivalence` supplies the actual Hom-colimit
comparison. Private proved categorical helpers supply inverse inclusion compatibility
and inversion of heterogeneous isomorphism comparisons. The generic inclusion
component lemma keeps concrete field operations out of elaboration. Abstract coefficient
transport identifies the cached finite category structures without expanding the
transferred field operations. The private irreducible `completionFinite` construction
exposes only its stage/family/shift API during assembly. The inverse shift is the
adjunction-induced shift; Mathlib supplies inverse exactness and triangle reflection.
No shared definition or public declaration signature changes.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.purFrameworkPbcCoefficientCategoryComparison`
(node `lem-pur-framework-pbc-coefficient-category-comparison`).
Added one split-off hole:
`WeilConjectures.fdCompletionFiniteStageLinear`
(node `lem-pur-completion-finite-stage-linear`).
There is no `sorry` in the item module. This is one upper hole decomposed into
one strictly smaller finite-linearity hole, not a net hole reduction.
The proof uses the already stated scalar-coherence, normalized common-stage descent,
and Hom-linear-equivalence theorems, whose existing holes are not changed here.

## No longer needed

Removed private proof imports `Sheaf.Paper.FdShiftTriangleReflection`,
`Sheaf.Paper.FdNormalizedIntegralCompletionComparison`, and
`Sheaf.CategoryTheory.SemilinearScalarLocalization`.
Added the private proof import `Sheaf.Paper.FdCommonStageComparisonDescent`.
The original proof dependencies `lem-fd-shift-triangle-reflection`,
`lem-fd-normalized-integral-completion-comparison`,
`lem-pur-semilinear-scalar-localization`, `lem-fix-scalar-completion-associator`, and
`lem-weil-finite-free-completed-scalar-comparison` need no separate invocation here:
the finite/scalar interfaces already supply their conclusions, and normalized
common-stage descent plus Mathlib handles the final shift/triangle assertions.
The completion and localization results remain dependencies of those interfaces;
this delivery does not claim that their modules leave the global target closure.
All existing public imports are retained for the statement. No module is withdrawn,
and no blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan did not mention the existing `fdNormalizedCommonStageDescent`
assembly interface. Its explicit stage/family equalities allow this theorem to retain
all finite inverse normalizations while reusing the common-stage construction.
The inverse adjunction compatibility is obtained by choosing the compatible inverse
shift, rather than asserting it for an arbitrary inverse shift supplied by a datum.
No disputed statement and no source-library edit.

## New nodes

`lem-pur-completion-finite-stage-linear` records the finite-field linearity step
only. Its pure-tensor formula, additive extension and identification of the two
normalized fraction maps imply linearity; it contains none of the scalar
coherence, pair-category equivalence, inverse shift, inverse integral formulas,
Hom-colimit, or counit/inclusion conclusions of the item. The statement includes
zero objects and morphisms, and does not assume faithful scalar transitions.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
