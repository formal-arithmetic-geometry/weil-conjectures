# AlgebraicGeometry.EtaleLogHom.existsUnique_logCotangent_characteristicQuotient_of_trivialBase

## Reason

The proof uses colimits and opposite categories, and the categorical definitions require the
same elaboration transparency settings already used by FineSaturatedLogBlowup and
LogDifferentialStalk. These commands were added for elaborating the private cocone and the
proof. There is no change to any existing declaration signature, public import, instance,
attribute, or mathematical definition. The item theorem is now proved.

## Old

```lean
set_option autoImplicit false
```

```lean
open CategoryTheory
```

## New

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.LogCotangentCharacteristicQuotientTrivialBase
--uses AlgebraicGeometry.EtaleLogHom.existsUnique_logCotangent_characteristicQuotient_of_trivialBase`
reported zero downstream modules and only the defining module as a use. No consumer
adaptation is required. The unfinished parent FreeCharacteristicRelativeNCCriterion still
needs this theorem's node; its statement and dependency are preserved.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.LogCotangentCharacteristicQuotientTrivialBase | G4 | Proof and private helpers elaborate; existing public theorem signature unchanged. |

No target statement or definition used by a target changes. The new definitions are private
explicit constructions of a pointed pullback neighbourhood, its point, and the induced cocone.

## Status

landed 20261023T123535-L-1207566 2026-10-23 (merge of deliver/G4/Sheaf.AlgebraicGeometry.LogCotangentCharacteristicQuotientTrivialBase)
