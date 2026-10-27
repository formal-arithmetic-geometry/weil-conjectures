# WeilConjectures.ConcreteIntegralProjection.coneComparison

## Reason

Write the identical endpoints explicitly to avoid inferring them through large functor constructions. The map and its meaning are unchanged by definitional equality; no consumer is adapted. Make this definition irreducible so later elaboration uses its explicit interface; the proof unfolds its defining equation explicitly. Target meanings are unchanged; the independent review can check the displayed constructions.

## Old

```lean
def coneComparison (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q) (n : ℕ) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso v (sfReductionRestricted l E W n)
```

## New

```lean
def coneComparison (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q) (n : ℕ) :
    ((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mappingCone v) ≅
      CochainComplex.mappingCone
        (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso v (sfReductionRestricted l E W n)

attribute [irreducible] coneComparison
```

## Users

`tools/downstream.py Sheaf.Paper.ConcreteIntegralProjectionCone --uses coneComparison` lists only the item itself, with zero downstream importing modules. Unfinished DAG parents still retain the item and its original statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConcreteIntegralProjectionCone | K2 | Identical endpoint types and actual map; explicit proof unfolding. |

## Status

landed 20261026T023420-L-563644 2026-10-26 (merge of deliver/K2/Sheaf.Paper.ConcreteIntegralProjectionCone)
