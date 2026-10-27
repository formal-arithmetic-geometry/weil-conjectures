## What changed

Completed twelve of the twenty-four existing theorem holes in
`Sheaf.Paper.CompactSupportRealizationFactorNormalization`. Public signatures,
definitions and public imports are preserved. Added proved private helpers for the
iterated mate identity, its counit formula and the component formula for the
categorical paste. Added a
private import for the existing section-normalized identity unitor. Local elaboration settings prevent large derived
functor and monoidal instances from unfolding during proof checking.

## Proved and sorry left

Closed holes (12): `geometricCharacteristic`, `geometricCharacteristic_prime`,
`geometricCharacteristic_ne`, `geometricCharacteristic_ne_fact`,
`ordinaryRestrictAdditive`, `ordinaryRestrictLimits`, `ordinaryRestrictColimits`,
`fieldPush_kInjective`, `coefficient_factorization`, `coefficient_proper_transpose`,
`structural_conjugacy`, `ordinaryPushIdentity_existsUnique`.

No holes added or split off. The remaining twelve holes, all attached to
`lem-zl-compact-support-realization-factor-normalization`, are:

- `integralComparison_normalization`
- `ordinaryRestrictionSquare_existsUnique`
- `ordinaryRestrict_kInjective`
- `realization_factor_normalization`
- `coefficient_open_unit`
- `coefficient_proper_isIso`
- `integral_naturality`
- `single_realization`
- `realization_identity_open`
- `coefficient_identity_open`
- `factorization_naturality`
- `completed_bridge`

The larger family construction, comparison inverse identities, scalar/open
normalization and completed composition retain their original statements and plans.
This is a partial proof delivery, not a decomposition of an upper hole.

## No longer needed

No modules or nodes are withdrawn. Removed unused private imports:

- `Sheaf.SixFunctors.IntegralOpenReductionComparison`
- `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence`
- `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation`
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.Paper.CompletedDirectImageLimits`

The dependency plan for the twelve untouched holes remains necessary; these
proof-only imports can be added when their declarations are actually used.

## Where the brief, the DAG or earlier work was wrong

No statement correction. `structural_conjugacy` follows directly from the existing
`Realizations.coherence` field and cancellation, so its proof needs no new induction.
The section-normalized identity unitor already exists as
`CompactSupportRealizationFactorization.ordinaryPushId`; reuse it and prove its
sectionwise uniqueness. These existing declarations avoid duplicating constructions.
The additional existing identity-unitor node is recorded in the DAG.

An attempted integral naturality proof needed the newer reconstruction declaration
`purNormalizedReconstructionOfScheme`, which was not visible to the compile environment.
That attempt and its imports were removed; the existing hole remains unchanged.

Validation: the first final check had no proof errors but exceeded the per-file
limit (65 seconds). The concrete mate rewrite was replaced by a proved abstract
counit helper, and asynchronous checking was restored. Final compile and delivery
preflight are pending.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
