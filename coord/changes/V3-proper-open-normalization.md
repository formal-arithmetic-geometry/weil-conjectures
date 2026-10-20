# AlgebraicGeometry.Etale.properOpenCoefficientInterchange

## Reason

The original choice projects a witness from the large simultaneous existential
`unboundedProperOpenInterchange`. Elaborating downstream equalities unfolds its
large auxiliary proof (`_proof_47`), and the unchanged item timed out at 60 seconds.
Extract its open-adjunction normalization into the small named theorem
`properOpenInterchange_normalization`, prove that normalization determines a unique
isomorphism, and choose that uniquely specified isomorphism. This keeps the same
source theorem and the same exchange and open-unit formulas. No mere-existence
witness is used as arbitrary data.

The proof of uniqueness is explicit: the hom of the restriction isomorphism is
prescribed on every object, so any two such isomorphisms are equal by Iso.ext and
NatTrans.ext. The interchange hom is then prescribed by its inverse restriction
and the open counit. Thus the previously chosen isomorphism and the new choice
agree. The theorem derives its witness from the original source theorem, without
adding assumptions or weakening any statement. The normal target-statement review
for a changed definition in the target import closure is applicable; this
uniqueness argument verifies that its mathematical meaning is unchanged.

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
  (properOpenInterchange_normalization A sq).choose
```

`properOpenInterchange_normalization` states existence and uniqueness of exactly
the exchange/open-unit/counit normalization already asserted in the old source.
It is proved in the same module. Every existing declaration signature, universe,
attribute and visibility is preserved. No source-library module is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperOpenCoefficientMate | V3 | Use the smaller normalization for the existing site proof and for the new coefficient proof. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Replace the old raw choice-specification projection by the new normalization theorem; all public signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed, unchanged | Indirect importer; no direct occurrence of the changed definition. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed, unchanged | Indirect importer; no direct occurrence of the changed definition. |

The table contains all three downstream modules reported by
`tools/downstream.py Sheaf.Paper.ProperOpenCoefficientMate --uses
properOpenCoefficientInterchange`, together with the item itself. Its direct name
search lists only the item and EtaleOriginProperOpenInterchange. The latter had no
current claim when adapted. The original consumer failed at its rewrite of
`Etale.properOpenCoefficientInterchange` by `hg`: the old raw chosen interchange
was absent from the target after the definition changed. Lines obtaining `le`,
`hle`, and `hge` now use
`(Etale.properOpenInterchange_normalization (ULift A) sq).choose_spec.1`.
This is the only change in that consumer.

## Status

landed 20261020T211842-L-3510578 2026-10-20 (merge of deliver/V3/Sheaf.Paper.ProperOpenCoefficientMate)
