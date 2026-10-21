# frobeniusPointIntegralSigma_existsUnique

## Reason

The pointwise specification repeatedly converts through the composite evaluation,
scalar restriction, and inverse-image functors. Express the same condition as
heterogeneous equality of their underlying functions, as in the earlier reviewed
sigma-specification change. `eq_of_heq` and function extensionality recover the
original condition, since both underlying section types are definitionally equal.
The chain map and its defining formula are unchanged. This delivery supplies the
linearity, differential compatibility and uniqueness proofs.

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

A search of all current Lean files and `tools/downstream.py
Sheaf.SixFunctors.FrobeniusPointTransport --uses frobeniusPointIntegralSigma_existsUnique`
finds no external users. The local choice definition retains the same witness
type and body. The proof of derived transport uses `eq_of_heq` to evaluate the
new specification. No target signature or mathematical meaning changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FrobeniusPointTransport | Z9 | Equivalent specification; proved here. |

## Status

landed 20261021T194614-L-1782105 2026-10-21 (merge of deliver/Z9/Sheaf.SixFunctors.FrobeniusPointTransport)
