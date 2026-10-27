## What changed

Filled seven of the sixteen theorem proofs in
`Sheaf.SixFunctors.CompletedShriekCompositionLaws`:
realization identities/composition and canonical-pair compatibility;
raw rational functor laws; comparison identity/cocycle; common-stage functor laws;
normalized compositor invertibility; the specified rational component; and the
specified common-stage component.

Realization uses `R.coherence` and cancellation of the actual recursive comparison
isomorphisms. Rational laws use the recorded localization functor on the full
constructible subcategory. The comparison cocycle cancels the middle reverse
refinement isomorphism. Compositor invertibility uses
`completedShriekFiniteEvaluation`, the explicit finite compositor (all its factors
are isomorphisms), and `calculus.isIso_iff_evaluations`.
The specified rational component uses `completedShriekIntegralComposition`,
`completedShriekSpecifiedIntegral`, and the uniquely normalized rational compositor.
The common-stage component uses the existing Qbar existence/uniqueness theorem
and functorial transport of the specified-rational heterogeneous equality.

Added only proved private helpers for the categorical calculations and finite
compositor invertibility. Existing signatures, definitions, public imports, and
remaining theorem bodies are unchanged. No new theorem obligations or nodes.
The route follows the existing node's steps 1, 2, 6 and 9; the uncompleted portions
of that plan remain for the nine original obligations.

Validation: single-file server compilation through `lcompile.py`, followed by
`deliver3.py`'s compile, axiom and packet checks. The exact compilation result is
recorded by those tools. No local Lake build was run.

## Proved and sorry left

Closed 7 holes, by declaration (all names are in
`WeilConjectures.IntegralSystemRealization`):

- `completedShriekRealizationLaws`.
- `completedShriekRationalLaws`.
- `completedShriekComposition_isIso`.
- `completedShriekComparisonCocycle`.
- `completedShriekCommonStageLaws`.
- `completedShriekSpecifiedRational`.
- `completedShriekSpecifiedCommonStage`.

Added 0 holes; split off 0 statements. These 9 original holes remain, each attached
to `lem-sf-completed-shriek-composition-laws` with its existing source and proof
docstring:

- `completedShriekRefinementLaws`.
- `completedShriekTowerRefinement`.
- `completedShriekAssociativity`.
- `completedShriekUnits`.
- `completedShriekChoiceIndependence`.
- `completedShriekIntegralBounds`.
- `completedShriekFiniteEvaluation`.
- `completedShriekIntegralComposition`.
- `completedShriekSpecifiedIntegral`.

This is a partial proof delivery, not a decomposition. The proof of compositor
invertibility still depends on the original finite-evaluation obligation; the
specified-rational proof still depends on the original integral-composition and
specified-integral obligations. No equality of system maps is inferred from finite
evaluations. The new private helpers are fully proved.

## No longer needed

Removed these unused private proof imports:

- `Sheaf.SixFunctors.AmbientProperOpenPasting`.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`.
- `WeilConjectures.Compactification.CategoryBaseChange`.
- `Sheaf.Paper.IntegralResidueTor`.
- `Sheaf.SixFunctors.CartesianOpenAdjunctionRestriction`.
- `Sheaf.Paper.CompactSupportUniformTorBound`.
- `Sheaf.Paper.OpenFiniteConstructibilityInterval`.
- `Sheaf.SixFunctors.OpenTensorNormalization`.
- `Sheaf.SixFunctors.FiniteCoverCTFLocality`.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`.
- `Sheaf.Paper.SfIntegralDirectImageConstructible`.
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
- `Sheaf.Paper.QcqsCompactSupportRealization`.

All names used by the completed proofs are provided by the existing public
statement imports. No public import was removed. No DAG node or entire library
module is declared unnecessary: the nine unfinished obligations retain their
existing mathematical proof dependencies, and other consumers may still use the
removed imports. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found in the portions proved. The common-refinement
cocycle in this file is specifically for one supplied refining compactification;
it follows directly from inverse cancellation and does not need choice
independence. The existing source proof describes this cancellation as well.

The completed-ring coordinate definitions need care during Lean rewriting:
explicit isomorphism arguments and generic categorical cancellation helpers avoid
unfolding the large site constructions. No definition or transparency setting
was changed.

Searches: `msearch.py` LeanFinder for conjugation preserving identity/composition
returned generic `Iso.conj_comp`/`Iso.homCongr_apply` facts; Loogle for
`Functor.map_comp` returned no identifier match; the grep service found generic
iso-transitivity calculations. Local `rg` located the precise `R.coherence`,
finite composition definitions, rational normalization and Qbar normalization
already used here. The Stacks proofs of `lemma-shriek-composition` and
`lemma-pseudo-functor` and the current blueprint compatibility unit were read.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
