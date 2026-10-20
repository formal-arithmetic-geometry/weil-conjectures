# AlgebraicGeometry.Scheme.OrderedExchange.reductionCounit

## Reason

Select the counit from the same bundled universal model as `reduction`.
The change is coupled to the reduction record repair, and keeps its canonical
universal counit and K-flat computation law. The old and new selected universal
pairs are related by their unique counit-compatible natural isomorphism; their
literal choices are not asserted to be definitionally equal.

## Old

```lean
def reductionCounit (T : Scheme.{t}) :
    DerivedCategory.Qh ⋙ reduction d T ⟶ reductionHomotopy d T :=
  (reduction_exists d T).choose_spec.choose
```

## New

```lean
def reductionCounit (T : Scheme.{t}) :
    DerivedCategory.Qh ⋙ reduction d T ⟶ reductionHomotopy d T :=
  (reductionData d T).counit
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | No direct use of this declaration; derived-limit complex-unit construction adapted for compile time in the same packet. |
| Sheaf.Paper.ProEtaleConstantReductionTower | G4 | Same universal constructions and normalized maps; proofs updated. |

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
