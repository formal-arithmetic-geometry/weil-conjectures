# Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections

## Reason
The proof uses the source-library chart construction for an arbitrary finite coordinate type. The old public imports exposed two large statement modules whose declarations were not needed by the proof. Their removal makes the module's public interface match the declarations it actually exports.

## Old
```lean
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
public import Sheaf.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
```

## New
```lean
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import Sheaf.AlgebraicGeometry.GeneratingSectionsStalkSpan
import Sheaf.AlgebraicGeometry.InvertibleStalkLinearEquiv
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
```

The two adapted consumers add the defining public module for `nonvanishingLocus` after the former re-export was removed. No declaration signature or definition was changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci | unclaimed | compiled unchanged |
| Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed | unclaimed | compiled unchanged |
| Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion | unclaimed | forced public import of `WeilConjectures.AlgebraicGeometry.Ample` |
| Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage | unclaimed | compiled unchanged |
| Sheaf.AlgebraicGeometry.SymmetricProductProperties | J8 | forced public import of `WeilConjectures.AlgebraicGeometry.Ample` |
| Sheaf.AlgebraicGeometry.SymmetricProductOverBase | unclaimed | compiled unchanged |
| Sheaf.AlgebraicGeometry.VeryAmpleSeparationCriterion | unclaimed | compiled unchanged |
| Sheaf.AlgebraicGeometry.SymmetricProductFinite | unclaimed | compiled unchanged |
| Sheaf.AlgebraicGeometry.SymmetricProductSurjective | unclaimed | compiled unchanged |
| Sheaf.AlgebraicGeometry.NoetherianSymmetricProductFiniteSurjective | E8 | compiled unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | compiled unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | V2 | compiled unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | N4 | compiled unchanged |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | F3 | compiled unchanged |

## Status
landed 20261018T062938-L-688019 2026-10-18 (merge of deliver/W2/Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections)
