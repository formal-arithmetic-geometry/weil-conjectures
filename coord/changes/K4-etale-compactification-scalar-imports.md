# EtaleCompactificationSheafScalarMap public imports

## Reason

Prune proof-only dependencies after replacing the generic tensor/bilinear proof plan by
adjunction units and graph normalization. The three public definitions and the theorem
signature remain textually unchanged. The source-library boundary is unaffected: no
`WeilConjectures` file is edited.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
public import Sheaf.SixFunctors.EtaleOpenTensor
public import Sheaf.Paper.ScalarPullbackRepresentativeData
public import Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionData
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleCompactificationGraphMap
public import Sheaf.SixFunctors.EtaleOpenTensorDefs
public import Sheaf.Paper.ScalarPullbackRepresentativeData
public import Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionData
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
```

Proof-only imports are private, including the proper-support composition, finite
compactification comparison, ordinary graph normalization, and scalar adjunction identities.
The returned duplicate `cached_sheafify` is removed; a private import of
`Sheaf.AlgebraicGeometry.SupportedExteriorProduct` supplies `supportedHasSheafify`, used only
as a local instance in this proof. This adds no public import or declaration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCompactificationSheafScalarMap | K4 | Proves the existing theorem; public declarations unchanged. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar | unclaimed | No adaptation: independently imports inverse-image exactness and cochain tensor universes; uses the scalar pullback API still exported here. |

`tools/downstream.py` lists exactly the latter consumer. No existing target statement or
definition is changed. The delivery consumer check validates the import interface.

## Status

landed 20261024T015156-L-2334385 2026-10-24 (merge of deliver/K4/Sheaf.EtaleCohomology.Purity.Smooth.EtaleCompactificationSheafScalarMap)
