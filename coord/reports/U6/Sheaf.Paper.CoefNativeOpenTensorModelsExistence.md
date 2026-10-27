## What changed

The item theorem now constructs its witnesses from two named intermediate obligations and combines
those obligations by an explicit `exact` proof. Two new modules were added:
`Sheaf.Paper.CoefNativeOpenTensorModelsDataExistence` supplies the system and finite model data,
and `Sheaf.Paper.CoefNativeOpenTensorGammaEvaluation` supplies the `GammaEvaluation` predicate.
The item DAG copy was updated so its proof and proof dependencies match this decomposition.

## Proved and sorry left

The original declaration `nativeOpenTensorModels_exists` is proved from the two intermediate
statements. The two new intermediate declarations retain one `sorry` each:
`nativeOpenTensorModels_data_exists` in
`lean/Sheaf/Paper/CoefNativeOpenTensorModelsDataExistence.lean` and
`nativeOpenTensorGammaEvaluation` in
`lean/Sheaf/Paper/CoefNativeOpenTensorGammaEvaluation.lean`.

## No longer needed

No imports from the original item were removed. The original seven planned proof dependencies
are replaced in the item proof by the two new intermediate declarations; their mathematical
dependencies are recorded on the new DAG nodes and remain needed by those obligations.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled model construction and the finite evaluation calculation into one
large theorem. The implementation route requires these as two independent interfaces before the
final existential can be assembled. No statement or definition in the existing library was
changed.

## New nodes

`lem-coef-native-open-tensor-models-data-existence` records the native system and finite model
construction obligation and its source dependencies.

`lem-coef-native-open-tensor-gamma-evaluation` records the exact finite-evaluation generator
calculation and its source dependencies.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
