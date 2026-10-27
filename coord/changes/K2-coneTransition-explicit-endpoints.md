# WeilConjectures.ConcreteIntegralProjection.coneTransition

## Reason

Write the identical endpoints explicitly to avoid inferring them through large functor constructions. The map and its meaning are unchanged by definitional equality; no consumer is adapted. Make this definition irreducible so later elaboration uses its explicit interface; the proof unfolds its defining equation explicitly. The two-summand map still uses unrestrictedTowerTransition on both summands. Its commutative-square proof is obtained degreewise from the same unrestrictedIntegralTransition naturality equation, by proof irrelevance the original value. It is not a transported intrinsic transition. Target meanings are unchanged; the independent review can check the displayed constructions.

## Old

```lean
def coneTransition (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q) (n : ℕ) :=
  CochainComplex.mappingCone.map
    (((sfReductionRestricted l E W (n + 1)).mapHomologicalComplex (.up ℤ)).map v)
    (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v)
    (unrestrictedTowerTransition l E W P n) (unrestrictedTowerTransition l E W Q n)
    ((unrestrictedIntegralTransition l E W n).naturality v)
```

## New

```lean
def coneTransition (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q) (n : ℕ) :
    CochainComplex.mappingCone
        (((sfReductionRestricted l E W (n + 1)).mapHomologicalComplex (.up ℤ)).map v) ⟶
      CochainComplex.mappingCone
        (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v) :=
  CochainComplex.mappingCone.map
    (((sfReductionRestricted l E W (n + 1)).mapHomologicalComplex (.up ℤ)).map v)
    (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v)
    (unrestrictedTowerTransition l E W P n) (unrestrictedTowerTransition l E W Q n)
    (by
      apply HomologicalComplex.hom_ext
      intro i
      exact congrArg (fun a ↦ a.f i) ((unrestrictedIntegralTransition l E W n).naturality v))

attribute [irreducible] coneTransition
```

## Users

`tools/downstream.py Sheaf.Paper.ConcreteIntegralProjectionCone --uses coneTransition` lists only the item itself, with zero downstream importing modules. Unfinished DAG parents still retain the item and its original statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConcreteIntegralProjectionCone | K2 | Identical endpoint types and actual map; explicit proof unfolding. |

## Status

landed 20261026T023420-L-563644 2026-10-26 (merge of deliver/K2/Sheaf.Paper.ConcreteIntegralProjectionCone)
