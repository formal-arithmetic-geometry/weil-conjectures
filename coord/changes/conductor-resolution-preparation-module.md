# Conductor resolution preparation module exports

## Reason

The remaining extension theorem needs separately stated tower/comparison steps. Those
steps must refer to the existing preparation and exact extension predicate without
importing the item theorem and forming a cycle. Move the existing preparation
section verbatim into the new ConductorResolutionPreparation module and publicly
re-export it from the item. All existing public names, signatures, bodies and
visibility are preserved; private helper names acquire the new module prefix.
The target statements and their definitions are unchanged.

## Old

The item contains the preparation section, from rationalInput_noetherian through
IsRationalConductorResolutionExtension, and has the following imports:

```lean
public import Sheaf.AlgebraicGeometry.SmoothNormalizedResolutionRule
public import Sheaf.TraceFormula.ConductorSmoothBaseChange
public import Sheaf.AlgebraicGeometry.NormalizedBlowup
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus
import Mathlib.AlgebraicGeometry.Noetherian
```

## New

Those imports and the complete preparation section are preserved in
Sheaf.AlgebraicGeometry.ConductorResolutionPreparation. The item imports:

```lean
public import Sheaf.AlgebraicGeometry.ConductorResolutionPreparation
import Sheaf.AlgebraicGeometry.ConductorResolutionComparison
import Sheaf.AlgebraicGeometry.NormalizedResolutionComparisonLaws
```

Its original public scope is preserved by the public preparation import. New
concrete tower constructors and their proved API live in ConductorResolutionTower;
they do not replace or alter any old declaration. The main theorem has precisely
its original signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConductorNormalizedResolutionExtension | W9 | Same public scope; proof assembled from new support modules. |

`tools/downstream.py` reports zero downstream modules. The anchored source import
search also finds no direct importers. The current item is needed by an unfinished
parent through the DAG, so no withdrawal is claimed. No existing module other than
the assigned item is changed.

## Status

landed 20261026T093016-L-3494238 2026-10-26 (merge of deliver/W9/Sheaf.AlgebraicGeometry.ConductorNormalizedResolutionExtension)
