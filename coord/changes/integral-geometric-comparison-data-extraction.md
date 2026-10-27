# AlgebraicGeometry.ProEtale.IntegralGeometricComparison

## Reason

The postponed component theorems need the diagram definitions, while the item theorem
imports those components. Move the definitions to a shared owner to avoid an import
cycle. The original module publicly reexports that owner. This is a relocation with no
change to an existing signature, definition body, instance or normalization equation.
The new SmoothPart, ReindexingPart and PurityPart records are literal subsets of Diagram.

## Old

```lean
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SmoothPurityNormalizedEquivalence
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.IntegralDirectImageTower
public import Sheaf.Paper.IntegralAdjunctionBijection
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.PurityCompactSupportTransport
public import Sheaf.Paper.PurityTateDatum
public import Sheaf.Paper.PurCompletedReindexingData
public import Sheaf.Paper.IntegralCompletedCoefficientTransport
public import Sheaf.Paper.ProperIntegralOrdinaryData
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.CompletedOpenExchangeTransport
public import Sheaf.Paper.CompletedExtensionZeroComparison
```

Module `Sheaf.Paper.IntegralGeometricComparisonRealization` contains all definitions
from PreservesKInjectives through Result and the realization theorem, with their existing
public names. Its public imports are the 26 lines reproduced verbatim in the new data module.
Every existing declaration signature and body is preserved verbatim in the delivery,
except that the realization theorem's proof is replaced by the actual assembly.

## New

```lean
public import Sheaf.Paper.IntegralGeometricComparisonData
```

The exact definitions from PreservesKInjectives through Result live in
`Sheaf.Paper.IntegralGeometricComparisonData`; the original module has
`public import Sheaf.Paper.IntegralGeometricComparisonData` and retains the theorem
with its original signature. The definition node owns the relocated declarations.
The original theorem node retains its declaration and mathematical statement, and adds
this definition owner to its statement dependencies. No target statement changes meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralGeometricComparisonRealization | F6 | Reexports all unchanged definitions; proves the assembly. |

`tools/downstream.py Sheaf.Paper.IntegralGeometricComparisonRealization --uses
AlgebraicGeometry.ProEtale.IntegralGeometricComparison.Diagram` found zero downstream
modules. A direct-import search likewise found none. Unfinished DAG parents retain the
same public names and their dependencies; no module is withdrawn.

## Status

landed 20261027T012830-L-2337459 2026-10-27 (merge of deliver/F6/Sheaf.Paper.IntegralGeometricComparisonRealization)
