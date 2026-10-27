# etaleSumCompactifiedComplexMap and etaleSumScalarComplexMap

## Reason

The explicit comparison factors for mapping a composite functor to complexes are
identity morphisms. Retaining them causes expensive elaboration of the graph and
scalar equations. Remove these identity factors from the two constructions; keep
the same sources, targets and canonical transformations. The identity-comparison
hom and inverse have identity components by definition, so the old and new maps
are equal by `HomologicalComplex.Hom.ext`, `Category.comp_id` and `Category.id_comp`.
This preserves the mathematical meaning of every statement, including targets.
No adopted source-library declaration is changed.

## Old

```lean
def etaleSumCompactifiedComplexMap
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (e : U ⟶ V) [Etale e] [IsSeparated e] (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
      (.up ℤ)).obj P ⟶ compactifiedEtaleDirectComplex A c P :=
  (NatTrans.mapHomologicalComplex (etaleCompactificationGraphMap A e c) (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)) (.up ℤ)).inv.app P

def etaleSumScalarComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶
      ((etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapHomologicalComplex
        (.up ℤ)).obj (coefficientExtendedComplex φ U P) :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
      ProEtale.etaleSheafExtendScalars φ V)) (.up ℤ)).hom.app P ≫
    (NatTrans.mapHomologicalComplex (etaleSumScalarSheafIso φ e).hom (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ U ⋙
        etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance)) (.up ℤ)).inv.app P
```

## New

```lean
def etaleSumCompactifiedComplexMap
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (e : U ⟶ V) [Etale e] [IsSeparated e] (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
      (.up ℤ)).obj P ⟶ compactifiedEtaleDirectComplex A c P :=
  (NatTrans.mapHomologicalComplex (etaleCompactificationGraphMap A e c) (.up ℤ)).app P

def etaleSumScalarComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶
      ((etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapHomologicalComplex
        (.up ℤ)).obj (coefficientExtendedComplex φ U P) :=
  (NatTrans.mapHomologicalComplex (etaleSumScalarSheafIso φ e).hom (.up ℤ)).app P
```

## Users

`tools/downstream.py` reports the item itself as the only textual user of either
changed declaration, and the following single downstream importer. The importer
uses the unchanged pure-tensor construction and theorem interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleSumCoefficientComputation | W8 | Prove the original coefficient computation with the identical canonical maps. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | H1 | Interface and statement unchanged; no source adaptation. |

## Status

landed 20261025T041314-L-1146018 2026-10-25 (merge of deliver/W8/Sheaf.Paper.EtaleSumCoefficientComputation)
