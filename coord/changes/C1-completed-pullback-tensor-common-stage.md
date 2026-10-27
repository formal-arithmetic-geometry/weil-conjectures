# CompletedPullbackTensorComparison construction extraction

## Reason

The common-stage proof needs both the existing scalar compatibility equation and
naturality of the fixed rational comparison. Its construction layer already takes
about 38 seconds to compile alone. Extract the existing finite, coherent, integral,
rational and scalar declarations to `CompletedPullbackTensorConstruction` and prove
rational naturality in `CompletedPullbackTensorNaturality`. This avoids a cycle and
keeps the common-stage proof separate from elaboration of the large constructions.
No existing public signature, universe, hypothesis, instance, definition body or
mathematical object changes. The original module publicly reexports the entire
construction layer. The integral scalar theorem retains its original `sorry`.
The original private sequence-ring equality remains a proved wrapper in the item
for `import all` consumers. No source-library module is edited.

## Old

The original public imports, verbatim:

```lean
public import Sheaf.Paper.FinitePullbackTensorComparison
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.CompletedPullbackTowerRealizations
```

All declarations were defined in
`lean/Sheaf/Paper/CompletedPullbackTensorComparison.lean`. In particular its
`canonicalCommonStagePullbackTensor_existsUnique` proof was `by sorry`.

## New

The original module's public import is:

```lean
public import Sheaf.Paper.CompletedPullbackTensorConstruction
```

`CompletedPullbackTensorConstruction` retains the old public imports verbatim and
all existing construction declarations with identical signatures and bodies. Only
`canonicalCommonStagePullbackTensor_existsUnique` and
`canonicalCommonStagePullbackTensor` remain defined in the original module. The
former is now proved; the latter's definition and signature are unchanged. The
new naturality theorem is a proof dependency only and is imported privately.
This is a relocation with a public reexport, not a change of a definition. Target
statements and all objects those statements use retain their meaning.

The DAG attaches moved declarations to
`def-pur-completed-pullback-tensor-construction`; the strict finite-evaluation
attachment is updated to the construction module. The original node retains its
statement and attaches the common-stage declarations to the original module.

## Users

The following table includes direct importers and every textual user of an existing
public declaration listed in the original node found by `tools/downstream.py --uses`.
Claims are the current shared records. No consumer source needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed in shared snapshot | Direct importer; unchanged signatures and data through reexport. |
| Sheaf.Paper.CompletedComparisonCanonicalIdentification | unclaimed in shared snapshot | Transitive user; unchanged signatures and data through reexport. |
| Sheaf.Paper.CompletedComparisonQuotientRealization | unclaimed in shared snapshot | Transitive user; unchanged signatures and data through reexport. |
| Sheaf.Paper.CompletedComparisonQuotientRealizationDefs | unclaimed in shared snapshot | Direct importer; unchanged signatures and data through reexport. |
| Sheaf.Paper.CompletedPullbackTensorComparison | C1 | Proof completed; other declarations reexported unchanged. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | F8 | Direct importer; unchanged signatures and data through reexport. |
| Sheaf.Paper.DerivedPullbackTensorIso | B4 | Direct importer; unchanged signatures and data through reexport. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed in shared snapshot | Transitive user; unchanged signatures and data through reexport. |
| Sheaf.Paper.IntegralPublishedFiniteEvaluation | unclaimed in shared snapshot | Direct importer; unchanged signatures and data through reexport. |
| Sheaf.Paper.IntegralPublishedTowerEvaluation | unclaimed in shared snapshot | Direct importer; unchanged signatures and data through reexport. |
| Sheaf.Paper.PodCompletionReindexModels | unclaimed in shared snapshot | Direct importer; unchanged signatures and data through reexport. |
| Sheaf.Paper.PodCompletionTensorNormalization | unclaimed in shared snapshot | Transitive user; unchanged signatures and data through reexport. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | G8 | Transitive user; unchanged signatures and data through reexport. |
| Sheaf.Paper.RegularCoefficientCoherentReduction | unclaimed in shared snapshot | Direct importer; unchanged signatures and data through reexport. |
| Sheaf.Paper.ReindexingSystemHomReductionSquare | D4 | Transitive user; unchanged signatures and data through reexport. |
| Sheaf.Paper.ScalarExtensionTowerComparisonData | unclaimed in shared snapshot | Direct importer; unchanged signatures and data through reexport. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed in shared snapshot | Transitive user; unchanged signatures and data through reexport. |
| Sheaf.SixFunctors.IntegralOrdinaryTowerComparison | unclaimed in shared snapshot | Direct importer; unchanged signatures and data through reexport. |

## Status

landed 20261027T180501-L-3865412 2026-10-27 (merge of deliver/C1/Sheaf.Paper.CompletedPullbackTensorComparison)
