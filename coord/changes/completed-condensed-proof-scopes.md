# CompletedCondensedCoefficients proof scopes

## Reason

The new categorical proofs use scoped object and functor projection notation.
They also keep the existing point and scheme adjunction definitions locally
irreducible during coefficient transport, avoiding expensive reduction of their
data. The full module compiled in 27.4 seconds after this elaboration adjustment. The
static interface checker treats the added `open scoped` command as an interface
change and requests this record. It changes elaboration within this file only;
Lean importers do not inherit open commands. No existing declaration signature,
visibility, definition, persistent attribute, instance, or public import changes.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
```

At the start of the namespace, the existing local reducibility attribute is moved
before the coefficient declarations, with the monoidal structure definitions also
kept irreducible to avoid expanding their construction during instance comparisons:

```lean
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
```

Within the private helper namespace:

```lean
attribute [local irreducible] pointUpperStarLowerStarAdjunction
  ProEtale.upperStarLowerStarAdjunction
```

After proving their generic ring compatibility, coefficient isomorphisms and the
colimit witness are kept locally irreducible:

```lean
attribute [local irreducible] localizationCoconeIsColimit
attribute [local irreducible] schemeCoefficientIso pointCoefficientIso
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedCondensedCoefficients | J1 | Scoped projection notation and local reducibility controls for the new proofs. |

`tools/downstream.py Sheaf.Paper.CompletedCondensedCoefficients --uses
completedCondensedRational` reports 1081 downstream modules and no external textual
use of that theorem. All downstream modules retain identical interfaces: this
record changes no declaration or definition. No consumer adaptation is needed.

## Status

landed 20261020T132011-L-1400682 2026-10-20 (merge of deliver/J1/Sheaf.Paper.CompletedCondensedCoefficients)
