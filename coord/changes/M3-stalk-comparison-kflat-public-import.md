# AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparisonTransformation

## Reason

Restore the quarantined item listed in coord/rework.tsv. Its public theorem mentions
CochainComplex.IsAcyclicTensorKFlat, defined by Sheaf.Algebra.Homology.KFlat.
The definition was available only through the private proof import of
Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso. A module's public section
cannot use a declaration available only through a private import. The upstream
StalkComparisonSourceTransport instead exports the distinct name IsKFlatTensor.
Add the missing direct public import of the existing definition. No statement,
definition, instance, proof, or source-library file changes.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore | M3 | Restored with the explicit public dependency required by its existing signature. |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso | quarantined; not adapted | Its archived proof applies this exact unchanged theorem; no adaptation required. |

A source search of lean/Sheaf and quarantine/Sheaf finds the second row as the
only direct importer and only external user of the declaration. The dependency
node and its unit route are preserved. Transitive quarantined consumers retain
exactly the same theorem and definition. No target meaning changes.

## Status

landed 20261020T145526-L-2407137 2026-10-20 (merge of deliver/M3/Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore)
