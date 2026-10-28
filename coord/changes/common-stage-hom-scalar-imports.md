# WeilConjectures.specifiedHomScalarRational_tower

## Reason

The finite-stage Hom tower module publicly imported DerivedPullbackTensorHom, which reaches
CommonStageInternalHomCoherence. Reusing the scalar tower in the common-stage proof would
therefore close an import cycle. Its theorem only needs FiniteRationalDerivedOperations and
SfScalarExtensionComposition. Both the scalar tower and scalar naturality DAG nodes also
listed def-weil-derived-pullback-tensor-hom, creating the same cycle in their statement and
proof dependencies. Remove that edge and name their actual finite-stage interfaces.
The two helper modules are unclaimed (checked on the project server).

## Old

```lean
public import Sheaf.Paper.DerivedPullbackTensorHom
```

Both helper nodes listed `def-weil-derived-pullback-tensor-hom` in `stmt_deps`, `proof_deps`
and the proof step's `uses`.

## New

```lean
public import Sheaf.Paper.FiniteRationalDerivedOperations
public import Sheaf.Paper.SfScalarExtensionComposition
```

The helper nodes replace the common-stage dependency by
`def-sf-finite-rational-derived-operations`; the tower node additionally cites
`lem-weil-scalar-extension-composition`. Declaration signatures, bodies and attributes
are unchanged. No definition used by a target changes meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SpecifiedHomScalarTower | unclaimed | Narrow public imports; theorem unchanged. |
| Sheaf.Paper.SpecifiedHomScalarRationalNaturality | unclaimed | Node dependencies corrected; Lean unchanged. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Direct importer; already publicly imports DerivedPullbackTensorHom. |
| Sheaf.Paper.SpecifiedHomScalarEvaluationArbitraryScheme | unclaimed | Interface preserved through SpecifiedHomScalarEvaluation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Interface preserved through SpecifiedHomScalarEvaluation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Interface preserved through SpecifiedHomScalarEvaluation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Interface preserved through SpecifiedHomScalarEvaluation. |
| Sheaf.Paper.CommonStageInternalHomCoherenceLemmas | S1 | Uses the scalar tower and naturality without a cycle. |
| Sheaf.Paper.CommonStageInternalHomCoherence | S1 | Uses the proved scalar coherence support module. |

## Status

landed 20261028T055750-L-805869 2026-10-28 (merge of deliver/S1/Sheaf.Paper.CommonStageInternalHomCoherence)
