# AlgebraicGeometry.tensorResolutionChartTensorIso_f

## Reason

Restore the quarantined module without mixing the two chart-model implementations.
Its upstream-tail import transitively imports the upstream single-tensor module,
which collides with the Sheaf single-tensor module already supplied by ChartModel.
The recorded global error names TensorResolutionSingleTensor_localInst1.
The two public theorem statements stay textually identical. The four local instance
implementations are aliases of the identical chart-model instances, and the proof
selects those chart-model instances explicitly, avoiding repeated normalization of
independent tensor structures. This is a definitionally equal presentation change;
no target meaning changes and no mathematical statement needs rereview.

## Old

Imports:
```lean
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartModel
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartTensorTail
```

Local instance definitions, verbatim from quarantine:
```lean
noncomputable local instance TensorResolutionChartTensorComponents_localInst1 (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionChartTensorComponents_localInst2 (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionChartTensorComponents_localInst3 (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionChartTensorComponents_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M
```

## New

```lean
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensor
```

Local implicit reducibility annotations support the affine-open, degree-embedding,
mapped-complex and tensor-instance conversions required by the original formulas.
They change no exported definition or statement. The tail argument is a proved
private lemma about arbitrary complexes. A further private API proves the complete
extension/naturality calculation over abstract categories and specializes it at a
bundled coefficient ring, avoiding repeated conversions between that ring and its
carrier when the chart component is checked by the kernel. These are proof lemmas
in this same module; no file or proof hole is split off. The chart
proof uses that lemma, the degree-zero single-complex formula, the extension
comparison, and naturality of the tilde tensor comparison. The unused homology
model and tensor-naturality imports are removed. No upstream file is
changed. The local instance definitions are:
```lean
noncomputable local instance TensorResolutionChartTensorComponents_localInst1 (X :
    Scheme.{u}) : MonoidalCategory X.Modules :=
  TensorResolutionChartModel_localInst1 X
noncomputable local instance TensorResolutionChartTensorComponents_localInst2 (X :
    Scheme.{u}) : MonoidalPreadditive X.Modules :=
  TensorResolutionChartModel_localInst2 X
local instance TensorResolutionChartTensorComponents_localInst3 (X : Scheme.{u}) :
    (curriedTensor X.Modules).PreservesZeroMorphisms :=
  TensorResolutionChartModel_localInst3 X
local instance TensorResolutionChartTensorComponents_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  TensorResolutionChartModel_localInst4 X M
```

## Users

`tools/downstream.py` with `--allow-missing --uses tensorResolutionChartTensorIso_f
 tensorResolutionMapExtendIso_inv_f` reports zero active library consumers, since
the item and its consumers are quarantined. The quarantine has these direct users:

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorNaturality | unclaimed | unchanged component statements |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorPositiveNaturality | unclaimed | unchanged component statements |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorTransport | unclaimed | unchanged component statements |

The direct consumers reference neither tensorResolutionChartHomologyIso, the two
TensorNaturality declarations, nor the upstream chart-tail theorem. The transport
and positive-naturality modules also import ChartComponents, which publicly imports
ChartModel. Thus the narrowed public imports require no consumer edit.

A trial restore of the consumer cluster stops at the independent root
Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso: the Sheaf and upstream
IsKFlatTilde modules both declare AlgebraicGeometry.isKFlat_tilde. Those modules are
not included in this delivery. No consumer edit is forced by a statement change.

## Status

landed 20261020T145445-L-2396811 2026-10-20 (merge of deliver/A8/Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorComponents)

Return ae853a6ccc repaired against the current quarantine source after the
intervening landing invalidated base 0dc07eb8c. Both public signatures were
compared byte for byte with the current archive and agree. The current rework
row still requests restoration for the duplicate-instance import failure;
this delivery reapplies the complete proof/import repair rather than removing
the archive or substituting an empty module.
