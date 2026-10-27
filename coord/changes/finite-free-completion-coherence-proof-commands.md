# Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence proof commands

## Reason

The identity proof constructs scalar multiplication and descends its natural isomorphism.
Unfolding the chosen sheaf tensor, quotient tower and Roos constructions during categorical
rewrites is expensive. Local irreducibility and transparency options keep those constructions
abstract. The static interface checker counts these commands as interface changes, so this
record documents them. No existing signature, visibility, public import or definition body
changes. All new helper definitions and theorems in the item are private and fully proved.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

There were no local irreducibility attributes and no later transparency-option changes.

## New

The initial option block adds the following command:

```lean
set_option backward.defeqAttrib.useBackward true
```

The following local commands occur after the relevant definitions:

```lean
attribute [local irreducible] quotientTower roosF SheafOfModules.monoidalCategory
attribute [local irreducible] scalarTensorSection arithmeticRoosMap
attribute [local irreducible] roosχ quotientMap quotientProduct
attribute [local irreducible] identityPresheafIso identitySheafIso
attribute [local irreducible] identityOrdinaryIso
```

Before the derived scalar-unit helper and again before the identity theorem the proof uses:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The original seven public declarations retain their signatures. Local attributes and
elaboration options affect this module's proofs only; downstream statements retain the same
meaning. No target definition changes and no consumer adaptation is necessary.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence` lists the
seven consumers below. The declaration-uses query for `finiteFreeCompletionExchangeIdentity`
finds only its own declaration in the item. No consumer file is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence | S1 | Identity proof and private helpers added; local proof commands documented above. |
| Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent | R3 | Same public signatures and definitions; no adaptation. |
| Sheaf.Algebra.Homology.SectionsScalarDerivedTransport | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.CategoryTheory.ToposScalarInverseExchangeMate | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.ExplicitScalarConeWordCoordinates | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.FiniteDerivedComparisonNormalization | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.InternalScalarMateTransitivity | J4 | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.ToposScalarMateTransitivity | G1 | Same public signatures and definitions; no adaptation. |

## Status

landed 20261024T020146-L-2563672 2026-10-24 (merge of deliver/S1/Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence)
