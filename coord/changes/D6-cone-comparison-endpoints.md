# WeilConjectures.ConcreteIntegralProjection.coneComparison

## Reason

Give the signed-cone isomorphism its explicit original inferred type, so Lean
does not unfold the entire isomorphism construction to find its endpoints.
The value, objects and maps are unchanged. No target statement changes.

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
```

The declaration now carries `[irreducible]`, so its explicit type is available
without unfolding the construction. The proof uses its defining equation explicitly.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Identical signed-cone comparison and type. |

The only downstream module ConcreteProjectionFieldDescent does not mention this name.

## Status

landed 20261025T201631-L-2591332 2026-10-25 (merge of deliver/D6/Sheaf.Paper.ConcreteIntegralProjectionCone)
