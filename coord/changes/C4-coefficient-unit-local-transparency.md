# AlgebraicGeometry.ProEtale.SpFiniteOrientation.coefficient_unit_tower_normalized

## Reason

Restore the assigned quarantined module and repair its local transparency setting.
The current rework row records an application type mismatch at the inverse realization
of `SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T)`.
`SpTowerClasses.Systems T (SpTowerClasses.Arings l E T)` uses evaluations of
`spCoefficientCommRings`, whereas `SpTowerShriek.S l E T` uses the same constant
quotient sheaves through `SpTowerShriek.B`. Marking the diagram locally irreducible
prevents elaboration from identifying them. Allow its normal unfolding within this
module. This changes neither the ring diagram nor the coefficient module.

## Old

The archived source has this local setting:

```lean
attribute [local irreducible] spCoefficientCommRings spCoefficientRings
```

Its public theorem signature is:

```lean
theorem coefficient_unit_tower_normalized
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u}) :
    IsSpNormalizedTower l E T (q.abelian T)
      ((SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj
        (SpTowerClasses.unit T (SpTowerClasses.Arings l E T)))
```

## New

The restored source uses:

```lean
attribute [local irreducible] spCoefficientRings
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers
```

The public theorem signature is verbatim the same:

```lean
theorem coefficient_unit_tower_normalized
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u}) :
    IsSpNormalizedTower l E T (q.abelian T)
      ((SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj
        (SpTowerClasses.unit T (SpTowerClasses.Arings l E T)))
```

The shared constant-sheaf and coefficient-field leaves are kept locally irreducible to
avoid their expensive unfolding; the diagram itself still unfolds for the required
category identification. The profiled repair compiled in 47.4 seconds, compared
with 60.4 seconds before keeping those leaves closed. Profiling options are removed
from the delivered source.

All archived declarations, imports, definition bodies and proof bodies are retained.
No global transparency attribute of either coefficient diagram is changed.
The DAG attachment, proof plan and dependency list stay as recorded.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteOrientationReduction | quarantined; not adapted | Its application of the theorem keeps the exact original type. |

No live Lean module imports the quarantined item. The archived direct importer
above uses the theorem at its normalized coefficient-unit reduction step. Its
unchanged archived source compiled against the repair in 46.2 seconds; the
validation copy was removed from the sandbox afterward. `downstream.py` cannot
index the absent item, so users were also searched in both live and quarantined
Lean sources.
No target statement or definition changes meaning, so this repair does not reopen
target statement review.

## Status

landed 20261027T205828-L-1622397 2026-10-27 (merge of deliver/C4/Sheaf.Paper.CoefficientUnitTowerNormalized)
