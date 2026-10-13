# AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_model

## Reason

The model theorem does not use open_kFlat_tensor_homology_comparison. That later
homology comparison is independent of constructing the present bounded model.
Its public import supplied a zero-map restriction instance. Use the existing proved
CategoryTheory.module_overFunctor_preservesZero from RhomIntoKInjectiveLocal,
registered only locally, instead. No new instance or signature is introduced.
The sole direct importer separately imports OpenKFlatTensorHomologyComparison,
so it retains that module's public declarations and instances.

## Old

```lean
public import Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison
```

## New

```lean
public import Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal

attribute [local instance] CategoryTheory.module_overFunctor_preservesZero
```

All other original public imports remain. The declaration's text and elaborated
proposition are unchanged; zero-map instance proofs are proof irrelevant.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorRelativeTorBound | unclaimed in the local claims snapshot | Sole direct importer; separately imports the removed module, so no adaptation is needed. |

Every indirect importer passes through this direct importer. The private proved
bound helper adds no API. The new construction and two new theorem modules add
public declarations but replace no existing definition or statement.

## Status

landed 20261013T115034-L-3327719 2026-10-13 (merge of deliver/W4/Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorModel)
