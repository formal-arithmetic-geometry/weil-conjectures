# AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback_composition_coherence

## Reason

Prove the existing coherence theorem through normalized ordinary adjunctions and exact-derived
localization. Its statement and all existing public declarations stay identical. The two
additional public imports are unnecessary: every name in the statement comes from
ProEtaleConstantRingPullbackComparison. All retained categorical proof imports are proof-only.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.IntegralFinitePullbackComposition
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
```

No existing definition or theorem signature changes. The new private structures and definitions
only package the data already uniquely determined by the existing normalization requirements:
adjunctions by their units, the direct-image comparison by its section formula, the ordinary
comparison by conjugation, and the complex comparison by its degree maps. They are used only in
proofs. No target statement or definition changes.

## Users

The read-only downstream.py command lists the seven modules below. The two direct importers
are FrobeniusPullbackComparisonCoherence and IteratedWeilCocycle. Both explicitly import
ProEtaleConstantRingComposition; IteratedWeilCocycle explicitly imports ProEtaleConstantRingMap.
No removed coefficient declaration is referenced by any of the other five modules. No consumer
adaptation is necessary. No listed consumer has a current claim in coord/claims.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence | P5 | One proof completed; unnecessary imports removed. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same declarations available through its existing imports. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same declarations available through its existing imports. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Direct consumer; coefficient composition already imported explicitly. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Direct consumer; both coefficient modules already imported explicitly. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same declarations available through its existing imports. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same declarations available through its existing imports. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same declarations available through its existing imports. |

## Status

landed 20261020T122122-L-480633 2026-10-20 (merge of deliver/P5/Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence)
