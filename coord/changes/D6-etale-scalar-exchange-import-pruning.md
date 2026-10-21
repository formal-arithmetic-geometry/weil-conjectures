# AlgebraicGeometry.Etale.exactDerivedBaseChangeMap_scalarExtension import pruning

## Reason

The complete proof uses the specialized scalar/pullback composition theorem and
categorical mate identities. Five original public imports are redundant for its
public statement. Remove these direct imports and keep the chosen Cartesian
square, exact exchange and coefficient comparison imports. The theorem's exact
signature and every definition it uses remain unchanged. Three fully proved private
helpers and three private proof imports support the proof. Local transparency
options assist elaboration and have no effect on the theorem's meaning.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.Paper.ProperOpenCoefficientRefinement
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.Paper.ProperOpenCoefficientRefinement

import Sheaf.Paper.ScalarPullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
```

No public declaration, statement, definition, attribute or target changes. The
remaining public imports provide all symbols in the existing theorem signature.
The private helpers do not occur in any public signature or definition body.
No module is withdrawn and no source-library module is edited.

## Users

The downstream declaration-use check and searches of the live and quarantined
Lean trees show no current Lean consumer of the item. Its unfinished DAG parents
still need its theorem, whose signature is unchanged. This record removes no
mathematical dependency from a parent's route.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange | D6 | Prove the original theorem and remove redundant direct public imports. |

There is no consumer adaptation and no target statement or definition change;
semantic target review is unaffected.

## Status

landed 20261021T130000-L-2477198 2026-10-21 (merge of deliver/D6/Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange)
