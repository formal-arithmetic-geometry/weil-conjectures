## What changed

Filled `WeilConjectures.isomorphismScalarComparisonAgreement` in
`Sheaf.Paper.IsomorphismScalarComparisonAgreement` using the two declared
proof dependencies of its current DAG node. Bundle the supplied coefficient
fields, apply `podCounitScalarWordCoordinates` to the supplied system D, and
pass its five effectivity assertions to `explicitScalarConeWordCoordinates`.
Unfold only the coordinate definitions and reassociate compositions to identify
the two normalizations. Their right-hand sides coincide; cancellation of the
invertible target coordinate proves the specified equality.

Added private proof imports of `Sheaf.Paper.PodCounitScalarWordCoordinates` and
`Sheaf.Paper.ExplicitScalarConeWordCoordinates`. Existing signatures, definitions,
public imports and the unit route are unchanged. No new nodes or statements.

Validation: lcompile.py compiled the final module without diagnostics (exit 0,
15.5 seconds). Both added imports pass tools/import_direction.py may. The
theorem signature and public import list match the current source verbatim;
all lines satisfy the 100-character limit.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.isomorphismScalarComparisonAgreement`
(node `lem-pod-isomorphism-scalar-comparison-agreement`).
Added 0 holes; no sorry remains in the delivered module.
The existing coordinate dependency theorems remain separate proof obligations;
they are used without copying or changing their statements or proofs.

## No longer needed

Removed the redundant direct private imports
`Sheaf.Paper.EffectiveComparisonRealizationModels`,
`Sheaf.Paper.IntegralComparisonSequenceSystems`, and
`Sheaf.Paper.IntegralComparisonRealizationModels`.
Their definitions remain available through existing public imports and the two
coordinate dependency modules. No dependency node or module is withdrawn or
claimed globally pruned: both proof dependencies of the current DAG are used.
The old five top-level tool approvals are retained because those results remain
needed by the coordinate lemmas and the statement's comparisons.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The current DAG already expresses the
three-step proof: the counit word equation, the explicit cone word equation in
the same coordinates, and cancellation. The older Lean docstring expands the
underlying normalization argument; its two existing child statements supply
that argument at this stage. The rework row records a historical transitive
ProjectiveLineGenusZero import failure; the assigned source is currently present
and is preserved, with its theorem proved rather than withdrawn.

Searches used msearch leanfinder (isomorphism cancellation), loogle
(`CategoryTheory.cancel_epi`) and grep (the comparison and coordinate names),
plus local searches of Sheaf and WeilConjectures. The categorical cancellation
API suffices for the final step; no source-library edit is needed.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
