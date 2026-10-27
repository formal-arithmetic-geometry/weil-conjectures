# AlgebraicGeometry.ProEtale.QuotientChange.scalarAmbientExchange

## Reason

Avoid repeated conversion through the enormous concrete derived adjunction and
pullback compositor when verifying the alias is its specified mate. The new body
uses the existing typed aliases adj and scalarPullbackSquare directly. Unfolding
these aliases gives exactly the previous condensedAmbientExchange construction.
The signature, canonical map, coefficient and geometric hypotheses are unchanged.
The defining module of scalarPullbackSquare becomes a public import because the
exposed definition now uses it in its data body. Kernel checking is unchanged.

## Old

```lean
def scalarAmbientExchange (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    F R f ⋙ L R c ⟶ L R a ⋙ F R f' := by
  unfold F L CondensedRing.moduleObjectDerivedPushforward
    CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.condensedAmbientExchange R sq
```

## New

```lean
def scalarAmbientExchange (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    F R f ⋙ L R c ⟶ L R a ⋙ F R f' :=
  (mateEquiv (adj R f) (adj R f')
    (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R sq).hom)).natTrans
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarGeometricExchangeRectangle | J6 | Its own routes and proof use the identical canonical mate through the typed aliases. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | R9 | Downstream importer; no occurrence of scalarAmbientExchange; its definitions and theorem statements are unchanged. |
| Sheaf.Paper.InternalScalarMateProjection | J3 | Downstream importer; no occurrence of scalarAmbientExchange; its definitions and theorem statements are unchanged. |

The read-only downstream.py --uses search reports the item module as the only
textual user, and the latter two modules as the only downstream importers.
No target statement refers to scalarAmbientExchange or this typed alias; this is
a presentation of the same data, not a change of mathematical definitions.
No consumer adaptation is required.

## Status

landed 20261024T015051-L-2318376 2026-10-24 (merge of deliver/J6/Sheaf.Paper.ScalarGeometricExchangeRectangle)
