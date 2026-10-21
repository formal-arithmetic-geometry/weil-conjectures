# AlgebraicGeometry.Etale.properOpenCoefficientInterchange

## Reason

The original definition selects a global family from the large conclusion of
`unboundedProperOpenInterchange`. Elaborating the assigned module with that body
exceeded the 60-second file limit; even small uses repeatedly reduce that entire
conclusion. Extract its exchange normalization into the proved theorem
`properOpenCoefficientInterchange_normalized_exists`, and select through that small
interface. Its exchange components determine the restriction isomorphism; taking
inverse open adjuncts determines the interchange itself.

`properOpenCoefficientInterchange_eq_recorded` proves equality with the original
selection. The data and all existing public signatures therefore have exactly their
previous meaning. There is no arbitrary witness of an undetermined existence claim.
Targets depending on this definition require the usual definition-change review;
the equality theorem provides the explicit semantic preservation argument.

## Old

```lean
def properOpenCoefficientInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i) :
    R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (unboundedProperOpenInterchange A).choose_spec.choose k r p i sq.toCommSq
```

## New

```lean
def properOpenCoefficientInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i) :
    R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (properOpenCoefficientInterchange_normalized_exists A sq).choose
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperOpenCoefficientMate | U3 | Extract normalization, prove equality with recorded choice, and close the coefficient transpose hole. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Its proof unfolds the old choice. Replace that unfolding by the equality theorem; retain all signatures. |

These are the two modules reported by
`tools/downstream.py Sheaf.Paper.ProperOpenCoefficientMate --uses properOpenCoefficientInterchange`.
The other transitive downstream modules are
`Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport` and
`Sheaf.Paper.ProEtaleCompositionTowerNormalization`; neither directly uses or
unfolds the changed declaration. Their mathematical statements are unchanged by
the proved equality.

## Status

landed 20261021T001147-L-1378604 2026-10-21 (merge of deliver/U3/Sheaf.Paper.ProperOpenCoefficientMate)
