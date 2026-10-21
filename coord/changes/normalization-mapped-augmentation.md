# AlgebraicGeometry.Etale.normalizationRestrictionAugmentation

## Reason

The original concrete composite is expensive to kernel-check when its quasi-isomorphism
proof is elaborated over the sheaf categories. Factor precisely that composite through
`normalizationMappedAugmentation`, a generic construction for an additive functor. Its
quasi-isomorphism proof uses only preservation of homology, before specialization to
etale inverse image. This makes the full file with four completed helper proofs compile
within the unchanged per-file allowance (55.9 seconds in the successful full-file probe).
No mathematical object, existing declaration signature or target statement changes.
The new definition has actual composite data and no postponed construction.

## Old

```lean
noncomputable def normalizationRestrictionAugmentation {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F) ⟶
        normalizationRestrictionComplex W F I :=
  ((upperStar AddCommGrpCat.{u + 1} W.hom).mapCochainComplexSingleFunctor 0).inv.app F ≫
    ((upperStar AddCommGrpCat.{u + 1} W.hom).mapHomologicalComplex (.up ℤ)).map I.ι'
```

## New

```lean
noncomputable def normalizationRestrictionAugmentation {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} W.hom).obj F) ⟶
        normalizationRestrictionComplex W F I :=
  normalizationMappedAugmentation (upperStar AddCommGrpCat.{u + 1} W.hom) F I
```

`normalizationMappedAugmentation L A I` is defined by
`(L.mapCochainComplexSingleFunctor 0).inv.app A ≫
(L.mapHomologicalComplex (.up ℤ)).map I.ι'`. Thus unfolding this single new definition
recovers the old body verbatim. Its definition is attached to the existing normalization
node; its private generic quasi-isomorphism helper is proved completely.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization --uses normalizationRestrictionAugmentation`
reports only the item itself, with three uses, and zero downstream modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization | V2 | The quasi-isomorphism proof specializes the generic lemma; the restricted resolution uses the identical augmentation. |

No consumer needs adaptation. The targets' meanings are identical by definitional
reduction; the independent reader should confirm this body-only factoring.

## Status

landed 20261021T194502-L-1721562 2026-10-21 (merge of deliver/V2/Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization)
