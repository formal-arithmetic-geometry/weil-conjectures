# WeilConjectures.GeneratorReduction.ordinaryU

## Reason

Declaration-level profiling found expensive kernel checks of `RhoNormalized` and
`systemDirectScalarIso_existsUnique` and its chosen comparison. Keep the exact scalar
restriction abstract while elaborating these later declarations, using the already
proved additive and exactness instances. The attribute is local and is placed after
`ordinaryUEvaluation`, whose construction uses the defining evaluation identity.

## Old

```lean
def ordinaryU (T : Scheme.{u}) : coefficientSequenceModules l E T ⥤
    constantTowerCategory l E T :=
  coefficientSequenceRestriction l E T ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (ordinaryH l E T)
```

## New

The definition above is unchanged. After `ordinaryUEvaluation`, add:

```lean
attribute [local irreducible] ordinaryU
```

This changes only elaboration within the current file. Public signatures, reducibility
seen by importers, and all mathematical statements remain unchanged.

## Users

`tools/downstream.py Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison --uses
ordinaryU` lists only the defining module as a direct user of the declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | X5 | Local elaboration only; no signature or body changed. |

The fourteen downstream modules receive the identical public interface, including the
original reducibility of `ordinaryU`. No consumer adaptation is necessary.

## Status

landed 20261025T203709-L-2841532 2026-10-25 (merge of deliver/X5/Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison)
