# WeilConjectures.LocallyClosedScalarPasting.locallyClosedScalarPasting

## Reason

The proof uses the existing finiteClosed operations and the canonical scalar unit.
Their two retained public imports supply every declaration needed by the module's
statements and definitions. Remove ten redundant or unused direct public imports.
No existing declaration signature, definition body, attribute or visibility changes.
The source-library tree is untouched.

## Old

```lean
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.FiniteClosedShriek
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.Paper.NormalizedOriginScalarComparisons
public import Mathlib.CategoryTheory.Adjunction.Basic
```

## New

```lean
public import Sheaf.Paper.FiniteClosedShriek
public import Sheaf.Paper.NormalizedOriginScalarComparisons
```

## Users

`python3 tools/downstream.py Sheaf.Paper.LocallyClosedScalarPasting --uses
locallyClosedScalarPasting` reports zero downstream modules and only the item's
own occurrence of the theorem. No existing Lean consumer requires adaptation.
The unfinished DAG parent lem-coef-finite-closed-shriek still needs this node;
its statement and the published declarations it will apply are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocallyClosedScalarPasting | N2 | One proof completed; imports reduced. |

## Status

landed 20261025T163920-L-899198 2026-10-25 (merge of deliver/N2/Sheaf.Paper.LocallyClosedScalarPasting)
