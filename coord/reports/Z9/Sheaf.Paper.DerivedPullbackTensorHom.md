## What changed

Replaced proof holes for integral and rational preservation of the permitted
internal-Hom pairs, the pointwise rational scalar comparison, and preservation
of permitted common-stage pairs at a larger stage. The proofs use the prescribed
completed integral comparison, the existing scalar-extension object formula,
and the integral scalar associator. Local transparency settings keep the
large chosen functors from unfolding during elaboration. Private helpers record
the underlying integral stage object and its iterated-extension associator.
All public definition bodies are preserved. The final existence theorem uses the
definitionally equal upstream `mkHom` constructor with explicit family, system
and universe parameters in place of `ofHom`; this avoids a 60-second elaboration
timeout. Its hypotheses and conclusion are definitionally unchanged. The matching
Lean attachment is updated, with the consumer check in
`coord/changes/z9-derived-hom-representative-elaboration.md`.

## Proved and sorry left

The patch supplies proofs for four of the twelve original holes and adds no
holes. The supplied proofs are:

- `WeilConjectures.integralHomScalarPair_permitted`.
- `WeilConjectures.rationalHomScalarPair_permitted`.
- `WeilConjectures.rationalHomScalarComparison_existsUnique`.
- `WeilConjectures.commonStageHomPairAtStage_permitted`.

The final complete module compiled cleanly in 48.0 seconds, with no warnings.
Delivery validation includes the axiom probe and the independent-reader checks.

Eight original holes remain, all attached to
`def-weil-derived-pullback-tensor-hom`:

- `WeilConjectures.rationalDerivedPullback_existsUnique`.
- `WeilConjectures.rationalDerivedTensor_existsUnique`.
- `WeilConjectures.rationalDerivedInternalHom_existsUnique`.
- `WeilConjectures.rationalPullbackScalarComparison_existsUnique`.
- `WeilConjectures.rationalTensorScalarComparison_existsUnique`.
- `WeilConjectures.commonStageDerivedPullback_existsUnique`.
- `WeilConjectures.commonStageDerivedTensor_existsUnique`.
- `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.

## No longer needed

None. Every existing public import supports the unchanged statements or
constructions. No module or node is withdrawn. The proofs implement their
existing docstring arguments without introducing a replacement proof route.

## Where the brief, the DAG or earlier work was wrong

The rework table still records this module and two direct imports in the
ProjectiveLineGenusZero quarantine cluster. An import probe confirms that the
published build supplies SfRationalizationKaroubi. Full-file diagnostics also
reach declaration elaboration rather than stopping at imports.

The latest blueprint, `literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md`, defines
ambient operations directly for condensed coefficients. The attached older
module still constructs operations on the completed-integral, rational and
common-stage categories. This delivery retains those public interfaces and
does not claim to reconcile that wider blueprint migration.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
