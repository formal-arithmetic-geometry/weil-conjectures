# WeilConjectures.integralPointTransportTowerRealization

## Reason

Package the supporting statement by its explicit canonical specification so that
its compiled artifact can be exported within the 60-second limit. This declaration
is not one of the targets in `lean/Challenge.lean`; that file and all target signatures
remain untouched. The expanded supporting statement was repeatedly kernel-checked
successfully but its artifact export made the file take 61--73 seconds.

The new predicate contains every original hypothesis and all seven conclusions:
the finite map formula on all complexes, both augmentation coordinates, both beta
coordinates, invertibility on constructible good representatives together with the
specified integral transport identity, and naturality for all derived morphisms.
There is no weakened or postponed condition inside the predicate.

`pointTransportTowerRealizationSpec_iff_expanded`, a fully proved private theorem
in the specification module, states the original expanded formula verbatim and
proves both directions by unfolding the named presentations. The full private
assembly proves the specification by constructing U, alpha, beta and proving each
of these seven conditions. Thus this packaging is an equivalent presentation,
not a replacement unproved theorem or a new assumption. Review of the statement's
meaning is explicitly requested. The associated construction presentation repair
is recorded separately in `G6-integral-point-transport-shared-data.md`.

## Old

```lean
theorem integralPointTransportTowerRealization (hl : l ≠ D.p) :
    ∃ (U : trfPointSourceTower D l E ⟶ trfPointTargetTower D l E)
      (α : trfPointSectionsComplex D l E ⟶
        trfPointSourceTower D l E ⋙ integralOperationsRoosFunctor)
      (β : integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom ⋙
          trfPointSectionsComplex D l E ≅
        trfPointTargetTower D l E ⋙ integralOperationsRoosFunctor),
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (n : ℕ) (i : ℤ)
        (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.obj
          (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        (((U.app P).app (op n)).f i) x =
          ((((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P).X i).val.map
            (proEtaleIsoCommaArrow (frobeniusPointIso D).hom
              (ProEt.mk (𝟙 (Spec (.of D.k))))).op
            (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)
              ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
                (ProEt.mk (𝟙 (Spec (.of D.k)))))
              ((((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.map
                (frobeniusPointRestriction D).op x)))) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ) (x : (P.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        ((α.app P).f i ≫ (CochainComplex.mappingCocone.fst
            (trfPointSourceEnd D l E P)).f i ≫
          (Pi.π (fun n ↦ ((trfPointSourceTower D l E).obj P).obj (op n)) n).f i) x =
          unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (P.X i)
            (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (i : ℤ),
        (α.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (trfPointSourceEnd D l E P)).v i (i - 1) (by omega) = 0) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫ (CochainComplex.mappingCocone.fst
            (trfPointTargetEnd D l E P)).f i ≫
          (Pi.π (fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n)) n).f i =
        ((trfPointSectionsComplex D l E).map
          (CochainComplex.mappingCocone.fst (trfPointSheafTargetEnd D l E P) ≫
            Pi.π (fun n ↦
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj
                (op n)) n)).f i) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫ (CochainComplex.mappingCocone.snd
            (trfPointTargetEnd D l E P)).v i (i - 1) (by omega) ≫
          (Pi.π (fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n)) n).f (i - 1) =
        (pointIntegralSections l E D.k).map
          ((CochainComplex.mappingCocone.snd (trfPointSheafTargetEnd D l E P)).v
              i (i - 1) (by omega) ≫
            (Pi.π (fun n ↦
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj
                (op n)) n).f (i - 1))) ∧
      (∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
        sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj P.obj) →
        IsIso (DerivedCategory.Q.map (α.app P.obj)) ∧
          frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj P.obj) ≫
            (pointFibreIntegralAmbient D l E).map
              ((integralDerivedPullbackComparison l E (frobeniusPointIso D).hom).hom.app P) ≫
            (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app
              ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj
                P.obj) ≫
            DerivedCategory.Q.map (β.hom.app P.obj) =
          (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map (α.app P.obj) ≫
            DerivedCategory.Q.map (integralOperationsRoosMap (U.app P.obj))) ∧
      (∀ (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (f : N ⟶ N'),
        (pointFibreIntegralAmbient D l E).map f.hom ≫
            frobeniusPointTransportIntegral D l hl E N'.obj =
          frobeniusPointTransportIntegral D l hl E N.obj ≫
            (pointFibreIntegralAmbient D l E).map
              ((integralDerivedPullback l E (frobeniusPointIso D).hom).map f.hom))
```

## New

```lean
theorem integralPointTransportTowerRealization (hl : l ≠ D.p) :
    pointTransportTowerRealizationSpec D l E hl
```

The original public imports are retained, with public prerequisites for the data
and specification. Proof implementations stay under private imports. The theorem
name, universe and parameters are unchanged.

## Users

A search in both Lean source roots found no call to the theorem outside its own
module. The consumers below and the published local Frobenius normalization
are checked unchanged. No consumer adaptation is included.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed in the claim snapshot | Import compatibility checked unchanged. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed in the claim snapshot | Import compatibility checked unchanged. |

## Status

landed 20261027T050602-L-240395 2026-10-27 (merge of deliver/G6/Sheaf.Paper.IntegralPointTransportTowerRealization)
