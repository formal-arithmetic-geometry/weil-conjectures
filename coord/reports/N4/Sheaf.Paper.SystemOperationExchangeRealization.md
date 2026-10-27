## What changed

In `Sheaf.Paper.SystemOperationExchangeRealization`, proved sectionwise direct-image
additivity from preservation of binary products, and obtained system K-injective
resolutions from Grothendieck abelianness of module sheaves in the actual site universes.
Added private proof imports for those existing results.

Derived `directImage_constructible` from the existing `directImage_roos` presentation
and `sfIntegralDirectImage_constructible`. Moved the unchanged Roos theorem before
its consumer. Derived `compactImage_constructible` by transporting the constructible
property through the existing `compactRealization`; moved it after that realization.
Added a private import of the existing isomorphism-closure theorem.

Identified the actual system direct-image functor with the existing varying-ring
pushforward for the adjacent ULift coefficient rings. Applied the existing
`pull_isRightAdjoint` and `extension_exact` theorems to prove
`systemPullback_isRightAdjoint` and `systemOpen_exact`. The identification and two
coefficient abbreviations are private proved helpers; they change no public interface.

All existing declaration statements, definition bodies and public imports are preserved.
The owning node records these proof dependencies and distinguishes the still-unproved
geometric presentations from their now-proved constructibility consequences.

Validation: the complete delivered module compiled cleanly through `lcompile.py` in
26.7 seconds. All existing signatures are preserved. The added private helpers have no holes.

## Proved and sorry left

Closed 6 of the 20 original holes, with no holes added:

- `WeilConjectures.FrobeniusExchange.systemDirect_additive`
- `WeilConjectures.FrobeniusExchange.system_hasKInjectives`
- `WeilConjectures.FrobeniusExchange.directImage_constructible`
- `WeilConjectures.FrobeniusExchange.compactImage_constructible`
- `WeilConjectures.FrobeniusExchange.systemPullback_isRightAdjoint`
- `WeilConjectures.FrobeniusExchange.systemOpen_exact`

The following 14 original named theorem holes remain, all attached to
`def-weil-system-operation-exchange-realization`:

- `WeilConjectures.FrobeniusExchange.systemDirectEvaluationOrdinary_eq`
- `WeilConjectures.FrobeniusExchange.systemPullEvaluationOrdinaryInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemDirectEvaluation_isIso`
- `WeilConjectures.FrobeniusExchange.systemExchange_evaluation`
- `WeilConjectures.FrobeniusExchange.systemOpenEvaluationInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenExchangeInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenScalarInv_isIso`
- `WeilConjectures.FrobeniusExchange.directImage_roos`
- `WeilConjectures.FrobeniusExchange.directImage_linear`
- `WeilConjectures.FrobeniusExchange.directAlpha_isIso`
- `WeilConjectures.FrobeniusExchange.compactRealization_existsUnique`
- `WeilConjectures.FrobeniusExchange.compactAlpha_isIso`
- `WeilConjectures.FrobeniusExchange.directIntegral_reduction`
- `WeilConjectures.FrobeniusExchange.compactIntegral_reduction`

These are unchanged theorem obligations with their original source citations and
natural-language proofs. No theorem has been split off and no new module has been added.
The two constructibility proofs intentionally use the existing geometric presentation
obligations; they do not claim to prove those presentations.

## No longer needed

None. No public import, dependency module, declaration or node is withdrawn. The
existing unit route is preserved. The newly added imports are private proof imports.

## Where the brief, the DAG or earlier work was wrong

The current source exists despite the historical quarantine/rework row, so the current
module was used and no archive was removed. The owning node originally had no proof
steps or proof dependencies; its copy now records the dependencies of the completed
proofs. Neither constructibility consequence needs a separate repetition of the
system-resolution construction once its existing presentation theorem is available.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
