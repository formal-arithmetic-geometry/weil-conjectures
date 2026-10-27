# WeilConjectures.trfAutomorphismSystemInverse

## Reason

Expose site transport followed by scalar restriction as separate functors.
The previous direct pushforward required Lean's kernel to identify nested
restriction-of-scalars objects with direct pushforward objects throughout the
scalar-extension comparison, exhausting the deterministic checking limit.
The new construction has exactly the same sections, restrictions, scalar
actions and action on module morphisms. No hypotheses or signatures change.

## Old

```lean
def trfAutomorphismSystemInverse :
    coefficientSequenceModules l E S ⥤ coefficientSequenceModules l E S :=
  SheafOfModules.pushforward (F := trfAutomorphismSystemSite g)
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (inv (trfAutomorphismCoefficientMap l E g)))
```

## New

```lean
def trfAutomorphismSystemInverse :
    coefficientSequenceModules l E S ⥤ coefficientSequenceModules l E S :=
  trfAutomorphismRawModules l E g ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (inv (trfAutomorphismCoefficientMap l E g)))
```

## Users

`tools/downstream.py Sheaf.TraceFormula.AutomorphismTensorReductionComparison
--uses trfAutomorphismSystemInverse` reports no downstream modules and only the
item itself as a declaration user. No other module needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.AutomorphismTensorReductionComparison | S1 | Same functor on sections, maps and scalar actions; proof conversion simplified. |

## Status

landed 20261026T070924-L-3699055 2026-10-26 (merge of deliver/S1/Sheaf.TraceFormula.AutomorphismTensorReductionComparison)
