# AlgebraicGeometry.Scheme.OrderedExchange.augmentation

## Reason

Construct the augmentation using the universal derived lift instead of
extracting a witness from the large uniqueness proposition. The new
`augmentation_normalized` proves its original representative formula, and
`augmentation_eq_choose` proves equality with the former selection from the
current `augmentation_existsUnique`. Thus the change retains the same unique
normalized augmentation for the selected reduction model.

## Old

```lean
def augmentation (T : Scheme.{t}) : diagonal (A := A) T ⟶ reduction d T :=
  (augmentation_existsUnique d T).exists.choose
```

## New

```lean
def augmentation (T : Scheme.{t}) : diagonal (A := A) T ⟶ reduction d T :=
  canonicalModelAugmentation (Functor.const ℕᵒᵖ) (reductionModule d T)
    (reductionData d T) (ordinaryAugmentation d T)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Textual match to another `augmentation` API; no semantic change. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | Same canonical reduction and representative equations; replace the expanded derived-limit complex unit by the existing library API, with its exact original formula proved generically, to repair compile time. |
| Sheaf.Paper.ProEtaleConstantReductionTower | G4 | Same universal constructions and normalized maps; proofs updated. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Textual match to another `augmentation` API; no semantic change. |

This table includes every textual hit from `tools/downstream.py --uses`;
name collisions are identified above. No adopted source-library file is changed. Direct
importers and the coefficient-comparison consumer are checked against the new
module. Statements involving the repaired universal pair retain their intended
meaning: the constant coefficient rings, finite quotients, strict transitions,
universal properties, normalizing equations and completion unit are unchanged.
Any target whose statement depends on a changed definition must undergo the
required statement review again. No target signature is changed.

## Status

landed 20261020T221158-L-4154121 2026-10-20 (merge of deliver/G4/Sheaf.Paper.ProEtaleConstantReductionTower)
