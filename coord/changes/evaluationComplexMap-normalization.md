# AlgebraicGeometry.Etale.OpenCounitFlatModels.evaluationComplexMap

## Reason

Repeated whole-file compiles exceeded the fixed 60-second limit. Targeted diagnostic runs localized expensive kernel conversion to the model-map normalizations. The former expression expanded the counit of the induced adjunction on complexes into three complex maps, including two identity boundaries. The new body uses that induced counit directly. The private generic theorem `mapComplex_counit_formula` proves that the former three-map expression equals the new expression for every additive adjunction. It preserves each degreewise ordinary sheaf evaluation map.

Explicit source and target complex types now prevent repeated inference through the comparison constructors. The version with these annotations compiled in 54.9 seconds.

The public mathematical meaning and the main theorem statement are unchanged. Targets using this definition should retain their statement review with the equality above checked; the definition change is explicitly submitted for independent review.

## Old

```lean
@[irreducible] def evaluationComplexMap (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (upperStar (ModuleCat.{u + 1} A) j ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} A) j)) (.up ℤ)).hom.app P ≫
    (NatTrans.mapHomologicalComplex
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit
      (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P
```

## New

```lean
@[irreducible] def evaluationComplexMap (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ⟶ P :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).counit.app P
```

## Users

`python3 tools/downstream.py Sheaf.Paper.EtaleOpenCounitFlatModels --uses coefficientComplexMap evaluationComplexMap` reports zero downstream modules and only this module as a textual user of either declaration. The quarantined attachment of the assigned item remains preserved; no parent or declaration is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleOpenCounitFlatModels | H1 | Model equation proofs use the equivalent direct complex map; the statement is unchanged. |

## Status

landed 20261025T050812-L-3844656 2026-10-25 (merge of deliver/H1/Sheaf.Paper.EtaleOpenCounitFlatModels)
