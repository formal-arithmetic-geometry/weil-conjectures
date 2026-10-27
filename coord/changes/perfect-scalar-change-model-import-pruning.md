# Sheaf.AlgebraicGeometry.PerfectScalarChangeModel public imports

## Reason

The delivered proof works with internal module objects and their categorical
flat/K-flat predicates. Three original public imports describe separate intrinsic
sheaf-module predicates or ordinary perfect complexes, none of which occurs in
this module's public signatures or definitions. Remove these unused imports to
reduce elaboration overhead and prune unused proof machinery. Every existing
signature and definition body is preserved. No mathematical definition or target
statement changes, and no consumer requires an adaptation.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
```

## New

```lean
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
```

The existing public import of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` is preserved.
The three removed APIs are not used by this module; the unchanged categorical
flatness and K-flatness statements use the source library API exported by the
retained imports. In particular this does not change the meaning of flatness or
of K-flatness.

## Users

`tools/downstream.py` lists the following thirteen downstream modules. None
mentions `IsFlatOnSite`, `IsKFlatIndependentCoefficients`, or `IsPerfectRingComplex`.
The sole direct importer is `LocallyPerfectScalarModel`; its statement uses only
the preserved internal-module local-model API. `ScalarSixCtf` independently imports
`PerfectRingComplexGeneral` where that API is relevant. No consumer file is edited.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.SixFunctors.LocallyPerfectScalarModel` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarCompositeModelPasting` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarRefinementClosureSquare` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarSixAdmissibleThickness` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarSixCanonicalExtensionComparison` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarSixCompactSupport` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarSixCtf` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarSixCtfGenerators` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarSixFiniteGeneration` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarSixNonfiniteGeneration` | unclaimed in local claim records | No signature, proof, or import adaptation. |
| `Sheaf.SixFunctors.ScalarSixPerfectExtension` | unclaimed in local claim records | No signature, proof, or import adaptation. |

## Status

landed 20261025T212724-L-220004 2026-10-25 (merge of deliver/C8/Sheaf.AlgebraicGeometry.PerfectScalarChangeModel)
