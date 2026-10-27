## What changed

Proved `smoothPullAugmentation_isIso` from ordinary pullback completeness,
`integralPullbackAugmentation_ambient`, and `canonicalCompletionUnitCriterion`.
The proof identifies the actual augmentation. It uses existing stated dependencies
and adds no holes. The lemma now states the coefficient-level result for any
separated, locally finite-type, quasi-compact morphism. Its original smooth
statement is the specialization used by `smoothPullToOrdinaryOnGood`, whose
signature and construction are unchanged.

Added the abstract `ordinaryMonoidal` presentation and used it in the coefficient
unit, tensor comparison, and ordinary left unitor. The two presentation signatures
are definitionally equal to their originals after unfolding the new wrapper; all
target statements and mathematical constructions retain their meanings.
Wrote the existing types of `orientation`, `ordinarySource`, `projection`,
`integralIso`, and `modelBack` explicitly, retaining their original bodies.
Category lookup prioritizes native category instances locally.
The change records are `coord/changes/S3-rational-smooth-purity-compile.md` and
`coord/changes/S3-smooth-pull-augmentation-generality.md`, and
`coord/changes/S3-canonical-purity-explicit-interfaces.md`.

Validation: the final single-file server compile passed cleanly in 52.8 seconds.

## Proved and sorry left

Closed 1 of the 7 original holes: `smoothPullAugmentation_isIso`. Added 0 holes.
The 6 remaining sorries are `finiteIntegration_smoothPurityMap`,
`orientation_existsUnique`, `smoothPullToOrdinary_existsUnique`,
`projection_isIso`, `integralMap_isIso`, and `rationalIso_scalar`.
All belong to `def-pur-canonical-rational-purity-realization`.

## No longer needed

The augmentation proof needs no direct Koszul-datum construction or auxiliary
prime: the published completion-unit criterion supplies that step. No baseline
imports or existing DAG dependencies were pruned. No new modules or nodes were
introduced; every added dependency already has its own stated node.

## Where the brief, the DAG or earlier work was wrong

The canonical module exceeded the fixed single-file compile limit at the start
of this session. The ordinary monoidal presentation required repeated comparison
of the expanded coefficient categories. Keeping this presentation abstract avoids
that repetition. The augmentation obligation can use the existing finite-Tor
ordinary-pullback completeness theorem and the published chain normalization.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
