# Quarantined import-source closure

## Reason

Landing fb958caf532 failed because the packet imported quarantined source modules.
The initial eight modules were restored and compiled with their consumers. Main
restored their cluster at 1a2b0743d6e, but a second red build quarantined 6019
modules again at 97ae054864b while delivery ran, so source presence failed again.
The subsequent restoration at 188066fac0c made the transitive sources available
on main again. Use that current restoration for the eight reported sources and their
unchanged dependencies.

## Old

The return found these modules absent from lean/ and present in quarantine/ at
the matching paths. Their current archives are the complete old signatures, imports,
definitions, statements, attributes, instances and proof bodies.

## New

The eight missing sources named by the return and their transitive dependencies
are now restored on main at 188066fac0c. Compare each complete source byte-for-byte
and omit the unchanged sandbox duplicates. Their original declarations, imports,
Lean attachments and dependencies remain available in the library. Nothing is
deleted, emptied or rewritten. A2's trace proof repair remains at 1dad6f3ccd8.

The broad 155-module validation stopped at unchanged KummerOrientation exceeding
60 seconds. A 31-module validation with only the eight immediate sources stopped
at unchanged DerivedPullbackTensorHom (64 seconds). Both failures are reported;
neither is claimed as a passing check. The original 23-module proof packet is
validated separately. No restored existing hole is counted as a G2 proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralComparisonSequenceSystems | G2 adaptation | Required source imports restored. |
| Sheaf.Paper.QuotientExpressionCoefficientData | G2 | Required source imports restored. |
| Sheaf.Paper.QuotientExpressionStrictKFlatTowers | G2 adaptation | Required source imports restored. |
| Sheaf.Paper.StrictPullbackEvaluationConstructor | G2 adaptation | Required source import restored. |

All restored modules, at unchanged original paths:

- `lean/Sheaf/Paper/DerivedPullbackTensorHom.lean` from `quarantine/Sheaf/Paper/DerivedPullbackTensorHom.lean`.
- `lean/Sheaf/Paper/IntegralSystemReductionFullyFaithful.lean` from `quarantine/Sheaf/Paper/IntegralSystemReductionFullyFaithful.lean`.
- `lean/Sheaf/Paper/SfRationalizationKaroubi.lean` from `quarantine/Sheaf/Paper/SfRationalizationKaroubi.lean`.
- `lean/Sheaf/Paper/StrictPullbackAdjointConstructor.lean` from `quarantine/Sheaf/Paper/StrictPullbackAdjointConstructor.lean`.
- `lean/Sheaf/Paper/StrictQuotientCompletedHorizontal.lean` from `quarantine/Sheaf/Paper/StrictQuotientCompletedHorizontal.lean`.
- `lean/Sheaf/Paper/StrictQuotientExpressions.lean` from `quarantine/Sheaf/Paper/StrictQuotientExpressions.lean`.
- `lean/Sheaf/Paper/StrictQuotientLevelwiseFlatModels.lean` from `quarantine/Sheaf/Paper/StrictQuotientLevelwiseFlatModels.lean`.
- `lean/Sheaf/Paper/StrictTensorAdjointConstructor.lean` from `quarantine/Sheaf/Paper/StrictTensorAdjointConstructor.lean`.

## Status

landed 20261027T205959-L-1641374 2026-10-27 (merge of deliver/G2/Sheaf.Paper.AmbientPullbackTensorCoherence)
