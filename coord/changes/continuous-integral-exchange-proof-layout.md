# integralConstructible_exchange_equality

## Reason

The proof now combines two one-sided adjunct normal-form calculations. Unused private abstract helpers and their scoped variables were removed from the item, so the static command-layout check requests this record. No public declaration signature, definition, universe, visibility or mathematical statement changes. Both comparison definitions and the specified exchange definition are the baseline ones. There are no forced adaptations or definition changes, and no target meaning changes.

## Old

```lean
theorem integralConstructible_exchange_equality
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    integralConstructibleSourceHom ℓ E k f g K ≫
        (boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ k sq).app
          ((integralScalarConstructible ℓ E X).obj K) =
      (integralScalarConstructible ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ k sq).app K) ≫
        integralConstructibleTargetHom ℓ E k f' g' K
```

The item also contained the private helpers CategoryTheory.Adjunction.coefficientMateCounit and CategoryTheory.Adjunction.coefficientExchange and their scoped category variables.

## New

```lean
theorem integralConstructible_exchange_equality
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    integralConstructibleSourceHom ℓ E k f g K ≫
        (boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ k sq).app
          ((integralScalarConstructible ℓ E X).obj K) =
      (integralScalarConstructible ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ k sq).app K) ≫
        integralConstructibleTargetHom ℓ E k f' g' K
```

These signatures are identical. Two proof-only imports supply the separate source and target adjunct normal-form calculations. The private helper section is removed; no importer could name its private declarations. The original scheme and coefficient variable types are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | A3 | proof and private helper layout changed; statement identical |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | same theorem signature and meaning; no adaptation |
| TargetsCheck | maintainer | same target closure statement; no adaptation |

## Status

landed 20261016T015245-L-720904 2026-10-16 (merge of deliver/A3/Sheaf.Paper.ContinuousIntegralExchangeEquality)
