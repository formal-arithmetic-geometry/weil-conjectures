# CompletedLineTensor proof context

## Reason

The completed-line coherence proof transports completeness through an isomorphism,
cancels the recorded scalar units, and restricts and localizes natural isomorphisms.
Those arguments need local unfolding of definitions previously marked irreducible.
A private instance supplies the already inherited additivity of rationalTwist.
The command checker requests this record for the added attribute commands and instance.
All 64 existing public declaration signatures, definition bodies, and public imports
are unchanged. No target statement or definition used by a target changes meaning.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

```lean
attribute [local irreducible] beta chi pairData power evaluation
```

The original file later contained:

```lean
attribute [local irreducible] unit ordinaryUnit
```

There was no private rationalTwist_additive instance or additional local
semireducibility command.

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
```

The additional namespace opening supplies tensor-product induction notation inside
this module; it exports no notation or declaration.

After the first command the proof temporarily restores unfolding of the two
coefficient sheaves, then restores their local irreducibility:

```lean
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted
```

After the second command it permits unfolding in the unit proof:

```lean
attribute [local semireducible] unit ordinaryUnit chi
```

Before integral beta restriction it exposes the equal-universe wrapper:

```lean
attribute [local semireducible] integralScalarExtensionOfUniverses
```

The added proved private instance is:

```lean
private instance rationalTwist_additive (L : integralTowerModules l E Y)
    [L.IsFiniteLocallyFreeOfRank 1] (hL : PreservesConstructible l E Y L) (m : ℤ) :
    (rationalTwist l E Y L hL m).Additive :=
  inferInstanceAs (ScalarLocalization.map _ _ _ (integralTwist l E Y L hL m)).Additive
```

This unfolds rationalTwist to its existing scalar-localization functor and reuses
Mathlib's additive instance. It changes no functor or Hom map and introduces no hole.
All reducibility attributes are local. Additional equality-transport, localization
and completeness helpers are private proved theorems. Existing public variables,
notation and signatures are retained.

## Users

`tools/downstream.py Sheaf.Paper.CompletedLineTensorCoherence --uses
rationalTwist_additive` reports four downstream modules and zero users of the new
private instance name. Their statements and definitions keep exactly the same meaning;
no consumer needs adaptation. No module belonging to another group is modified.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedLineTensorCoherence | J6 | Twelve existing proofs completed; private proof context added. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | R8 | Existing interface and meaning preserved; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | D9 | Existing interface and meaning preserved; no adaptation. |
| Sheaf.Paper.ScalarCompletionAssociator | unclaimed | Existing interface and meaning preserved; no adaptation. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | A8 | Existing interface and meaning preserved; no adaptation. |

## Status

landed 20261021T182318-L-1175256 2026-10-21 (merge of deliver/J6/Sheaf.Paper.CompletedLineTensorCoherence)
