# Sheaf.Paper.IntegralOperationsScalarComparisons

## Reason

The completed proofs use the two public statement imports and the two
proof-only change-of-rings imports. CoefficientExtensionFinite remains imported for
the fixed unit route. The other unused proof-plan imports were removed. The module's public declarations and signatures are unchanged.

## Old

```lean
public import Sheaf.Paper.IntegralOperationsScalarExtension
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.CompactSupportRoosCofinality
import Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.DerivedCompleteKoszulReconstruction
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.IntegralScalarExtensionUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.WeilCompletedTensorReflector
```

## New

```lean
public import Sheaf.Paper.IntegralOperationsScalarExtension
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralOperationsScalarComparisons | Y3 | proof imports are pruned; public declarations are unchanged |

## Status

landed 20261019T034354-L-426362 2026-10-19 (merge of deliver/Y3/Sheaf.Paper.IntegralOperationsScalarComparisons)
