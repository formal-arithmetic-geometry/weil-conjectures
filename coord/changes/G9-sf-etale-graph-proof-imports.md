# AlgebraicGeometry.Etale.sfEtaleGraphProjectionArbitraryBase

## Reason

Remove unused public proof-plan imports from the item. Its declarations only
need the ambient projection, specified source graph comparison and exact
pullback tensor comparison interfaces. No declaration signature or definition
body changes. The two new proof imports are private.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
public import Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence
public import Sheaf.CategoryTheory.UnitAdjunctTensorAction
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
```

## New

```lean
public import Sheaf.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
public import Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase | G9 | Compiles with reduced imports; all four public declarations retain their original types and bodies except the theorem proof. |

A search of all Lean files found no direct importers of the item. DAG parents
with unfinished proofs keep the same four declarations available and require
no adaptation. No target statement or definition is changed.

## Status

landed 20261025T095409-L-3397528 2026-10-25 (merge of deliver/G9/Sheaf.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase)
