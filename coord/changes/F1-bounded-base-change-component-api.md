# boundedConstructiblePullbackSquareComparison_app

## Reason

The target adjunct calculation needs the component formula for the specified bounded
pullback-square comparison. Reducing projection-headed concrete functor structures forces
large derived-category normalization. A generic isomorphism component calculation avoids it.

The source module is unclaimed. This addition preserves every existing declaration,
definition, visibility, attribute and import, including the concurrently landed adjunct
presentation of base change and its three API theorems. No target definition changes.

## Old

There was no declaration named `boundedConstructiblePullbackSquareComparison_app`.
Every existing declaration remains verbatim.

## New

One proved component lemma is added to
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`:

```lean
lemma boundedConstructiblePullbackSquareComparison_app (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y)) :
    (boundedConstructiblePullbackSquareComparison Λ ℓ k sq).app K =
      ((boundedConstructibleUpperStarComp Λ ℓ k f' g).app K).symm ≪≫
        (eqToIso (by simp only [sq.w]) :
          boundedConstructibleUpperStar Λ ℓ k (f' ≫ g) ≅
            boundedConstructibleUpperStar Λ ℓ k (g' ≫ f)).app K ≪≫
        (boundedConstructibleUpperStarComp Λ ℓ k g' f).app K
```

Its private generic helper `triple_app` computes the component of three composed natural
isomorphisms by reflexivity. The public result applies that helper to the existing definition.
There is no hypothesis change, data construction or new hole.

## Users

The declaration is new; there are no existing textual users. Existing importers see precisely
the same old definitions and theorems, and no existing importer requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | One proved component lemma and its private generic helper added. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | F1 | Uses the component lemma in its pull-square cube proof. |

## Status

landed 20261016T054835-L-156980 2026-10-16 (merge of deliver/F1/Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct)
