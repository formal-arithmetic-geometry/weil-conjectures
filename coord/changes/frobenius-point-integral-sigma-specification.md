# frobeniusPointIntegralSigma_existsUnique

## Reason

The original pointwise condition forced kernel reduction of the full composite
sections and inverse-image functors, even for the statement and its choice
construction. The unmodified file exceeded the 60-second compile limit. Writing
the same condition as heterogeneous equality of the underlying functions removes
that repeated conversion. The otherwise unmodified file then compiled in 18.1 seconds.

The domains and codomains of these functions are definitionally the original
section types. Thus `heq_eq_eq` followed by `funext_iff` recovers exactly the old
pointwise condition; this changes neither the unique chain map nor any target's
mathematical meaning. The coefficient-linearity and chain-map proofs are supplied,
not assumed. The public sigma definition keeps its signature and body.

## Old

```lean
theorem frobeniusPointIntegralSigma_existsUnique
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! f : ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
               (.up ℤ)).obj K),
      ∀ (i : ℤ) (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        f.f i x = (K.X i).val.map (frobeniusPointRestriction D).op x
```

## New

```lean
theorem frobeniusPointIntegralSigma_existsUnique
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! f : ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
               (.up ℤ)).obj K),
      ∀ i : ℤ, HEq (fun x ↦ f.f i x)
        (fun x ↦ (K.X i).val.map (frobeniusPointRestriction D).op x)
```

## Users

`tools/downstream.py --uses frobeniusPointIntegralSigma_existsUnique` finds only the item
module. Its choice construction needs no adaptation because the existential
witness has precisely the same type. No other module refers to this theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FrobeniusPointTransport | G9 | Equivalent specification; witness type unchanged. |

## Status

landed 20261021T101054-L-6471 2026-10-21 (merge of deliver/G9/Sheaf.SixFunctors.FrobeniusPointTransport)
