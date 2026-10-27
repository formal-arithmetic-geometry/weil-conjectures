# Compact-support coefficient transport module split

## Reason

The assigned file elaborates completely but takes 89 seconds after the new proof
and the extraction of generic helpers. Profiling identifies independent costs in
ordinary system transport and strict/derived limit normalization. Isolate the
ordinary construction to satisfy the 60-second per-file limit. This changes the
module interface by adding a public re-export, but no existing declaration type,
visibility, attribute, universe, instance registration or definition body changes.
No mathematical statement is repaired or weakened.

## Old

The declarations from `rightUnitApp` through `systemProjection` were defined in
`Sheaf.Paper.SemilinearCompactSupportCoefficientTransport`. In particular:

```lean
def systemProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    systemSupport l E c ⋙ (systemScalarData l E F i Y).scalar.T ⟶
      (systemScalarData l E F i X).scalar.T ⋙ systemSupport l F c
```

## New

Those declarations have the same names, signatures and bodies in
`Sheaf.Paper.OrdinaryCompactSupportCoefficientTransport`. The original module
adds `public import Sheaf.Paper.OrdinaryCompactSupportCoefficientTransport` and
retains every existing public import. The signature above is unchanged. Generic
private proofs are isolated as proved theorems in `CompactSupportScalarProofs`;
the new pullback argument uses the proved `SystemRestrictionInverseMateEvaluation`.
No existing public declaration moves outside the re-exported interface.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | K1 | Publishes the same declarations by re-export; retains limit definitions. |
| Sheaf.Paper.NativeConstantRestrictionAcyclicity | unclaimed | Unchanged; elaborates over limit against both versions. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Unchanged; same kernel error against both versions. |
| Sheaf.Paper.CompactSupportCondensedRealization | J1 | Unchanged; elaborates over limit against both versions. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Compiles unchanged against the re-export. |

| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.CompactSupportScalarShiftStructures | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.NativeConstantSupportModel | claim exists; not adapted | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.OrdinaryScalarBalancingLevel | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.OrdinaryScalarReductionGenerators | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.ReconstructedPairRefinementData | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.ScalarReductionTowerBalancing | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.ScalarSourceCounitUniversal | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.ScalarTargetCounitUniversal | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |
| Sheaf.Paper.StrictScalarMateEvaluationData | unclaimed | Transitive name user; public signatures and data bodies preserved by re-export. |

The four direct importers are compiled from temporary unchanged copies, then
removed from the sandbox; no consumer modification is proposed. The report records
comparative baseline compiler results: two already exceed 60 seconds, and
`CompactSupportRealizationFactorization` already has an unknown-instance kernel
error with the original published library. All four packet modules pass the
single-file acceptance check.

## Status

landed 20261026T222727-L-687038 2026-10-26 (merge of deliver/K1/Sheaf.Paper.SemilinearCompactSupportCoefficientTransport)
