# AlgebraicGeometry.ProEtale.CondensedRing.openExtension_constructible_finiteTor

## Reason

The proof uses local irreducibility attributes to prevent elaboration from unfolding
large internal-Hom constructions and the named pullback and derived tensor functors.
The static command classifier requires a change record for these attribute commands.
They are explicitly local and do not affect importing modules. Two proved private
helpers control definitional conversion of Tor amplitude and stratification fields.

## Old

No local transparency attribute commands occurred in the item module. The theorem
had its present signature and proof `:= by sorry`.

## New

```lean
attribute [local irreducible] upperStar upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
```

After the proved definitional tensor helper:

```lean
attribute [local irreducible] derivedTensor
```

The theorem signature and all eight public imports remain verbatim. Its proof is
complete. The two added theorem declarations are private and proved. The only new
options are scoped transparency options on the private tensor helper. There is no
change to any definition or target statement, and no target review is reopened.

## Users

`tools/downstream.py Sheaf.Paper.OpenExtensionConstructibleFiniteTor --uses
openExtension_constructible_finiteTor` reports zero downstream modules and the item
itself as the sole textual declaration user. Future parents retain precisely the
same public theorem and imports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OpenExtensionConstructibleFiniteTor | W4 | Original hole closed; private helpers and local proof transparency only. |

## Status

landed 20261024T021632-L-2839058 2026-10-24 (merge of deliver/W4/Sheaf.Paper.OpenExtensionConstructibleFiniteTor)
