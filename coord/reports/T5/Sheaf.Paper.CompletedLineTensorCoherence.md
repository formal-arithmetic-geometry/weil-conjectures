## What changed

Completed `WeilConjectures.CompletedLineTensor.ordinaryUnit_existsUnique` using the
existing chain multiplication isomorphism and the universal left-derived counit.
A proved private helper descends their composite through localization. Existence
holds on every complex; uniqueness follows by fully faithful precomposition with
the existing localization of flat-term K-flat complexes.

Added the proof-only `import all Sheaf.Paper.IntegralOperationsWellDefined` to reuse
its proved private `integralOperationsGoodLocalization_isLocalization` theorem.
Also used a proof-only `import all Sheaf.Paper.FiniteFreeCompletedScalarComparison`
to reuse its proved cochain model and counit identification; its existing public
import remains unchanged.
Simplified the existing `exact` proof's additivity step using Mathlib's direct binary-product lemma,
and unfolded the rationalized functor once before inferring its additivity.
All public signatures and public imports remain unchanged. The existing
`comparisonComplex` and `scalarAssociatorComplex` bodies now explicitly unfold only
their complex wrappers before applying the same termwise comparison; their data
remain definitionally equal to the original bodies.
No source-library module is changed. The cochain model avoids repeatedly expanding the chosen homotopy-derived witness.
Local elaboration controls are documented in
`coord/changes/T5-completed-line-unit-proof-context.md`.

## Proved and sorry left

Closed 1 of the original 11 holes:
`WeilConjectures.CompletedLineTensor.ordinaryUnit_existsUnique`.
Added 0 holes; split off 0 statements. All five new private helpers are proved:
`line_model_functor`, `line_model_complex`, `line_model_counit`,
`line_derived_unit`, and `line_unit_from_model`.

The 10 remaining original holes are all in namespace
`WeilConjectures.CompletedLineTensor`, with node
`lem-pur-completed-line-tensor-coherence`:

- `evaluation_existsUnique`
- `complete`
- `pairData_existsUnique`
- `associatorData_existsUnique`
- `beta_natural_evaluation`
- `scalar_coherence`
- `tower`
- `integralTwist_linear`
- `canonical_restriction`
- `rational_diagonal`

## No longer needed

No existing import or module is withdrawn. The unit proof uses Mathlib localization,
the chain identity multiplication, and the existing good-complex localization theorem;
it does not need the full `OrdinaryLineDerivedScalarComparison` package.
The other planned dependencies remain relevant to the untouched holes and are not
claimed as globally pruned. No DAG node or unit is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG suggests importing `IntegralLineTensorCompleteness` to prove `complete`.
Its current Lean module imports this item and proves `integralLineTensor_complete`
by applying `CompletedLineTensor.complete`; that route would be cyclic. This partial
delivery does not alter the completeness statement or that consumer.

The completed scalar wrappers are locally irreducible in this item, so extraction
of the universal counit and identification of its chain normalization require
explicit unfolding. The standard derived-category construction can also cause costly
elaboration; file-local controls keep it irreducible and select the existing
integral-tower instance. Additional local controls bound the cochain-model and
rationalization elaboration without changing their definitions. No mathematical definition is repaired.

Updated the existing coherence node with the concrete localization proof of the unit
and its existing good-complex localization dependency. No new DAG node is needed.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
