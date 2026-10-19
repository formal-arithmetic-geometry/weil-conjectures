## What changed

Proved eight declarations in `Sheaf.Paper.SystemOperationExchangeRealization`.
The proofs establish additivity, K-injective resolutions, the varying-ring right
adjoint and open exactness, ordinary direct-image evaluation, direct and compact
constructibility, and the direct integral reduction equation. Added proof-only
imports for the varying-ring operations, universe-parametrized K-injective
resolutions, and Grothendieck K-injective resolutions. The sheafification
instances are temporarily removed in a section to keep elaboration within the file limit.
All declaration signatures are unchanged.

## Proved and sorry left

Closed 8 of the original 20 holes:
`systemDirect_additive`, `system_hasKInjectives`, `systemPullback_isRightAdjoint`,
`systemOpen_exact`, `systemDirectEvaluationOrdinary_eq`, `directImage_constructible`,
`compactImage_constructible`, and `directIntegral_reduction`.
Added 0 holes.

The following 12 original holes remain, each attached to
`def-weil-system-operation-exchange-realization`:

- `systemPullEvaluationOrdinaryInv_isIso`
- `systemDirectEvaluation_isIso`
- `systemExchange_evaluation`
- `systemOpenEvaluationInv_isIso`
- `systemOpenExchangeInv_isIso`
- `systemOpenScalarInv_isIso`
- `directImage_roos`
- `directImage_linear`
- `directAlpha_isIso`
- `compactRealization_existsUnique`
- `compactAlpha_isIso`
- `compactIntegral_reduction`

## No longer needed

No original imports, nodes, or modules were removed. The added imports are used by
the completed proofs. The direct constructibility proof uses the existing
`directImage_roos` declaration, and compact constructibility uses the existing
`compactRealization_existsUnique` declaration, so neither dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The K-injective theorem requires explicit universe parameters for the independent
coefficient universe. The right-adjoint and exactness proofs require transport from
the generic varying-ring operations through definitional equality of the concrete
coefficient sequence. The direct reduction calculation is proved once for an
abstract system operation and then specialized to direct image; this avoids
unfolding the large derived direct-image definition while preserving the original
statement and hypotheses.

## New nodes

None.

The instance-scope change is recorded in
`coord/changes/system-operation-elaboration.md`.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
