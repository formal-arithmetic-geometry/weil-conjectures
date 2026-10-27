# AlgebraicGeometry.Etale.OpenCounitFlatModels.coefficientComplexMap

## Reason

Repeated whole-file compiles exceeded the fixed 60-second limit. Targeted diagnostic runs localized expensive kernel conversion to the model-map normalizations. The former expression composed the degreewise coefficient comparison with the inverse of the complex comparison attached to the identity natural isomorphism. That inverse has identity components, so it is the identity complex morphism under the canonical definitional identification. Removing it preserves the degreewise map and avoids expensive comparison of the two nested complex presentations. The private generic theorem `mapComplex_comp_identity` proves the cancellation for arbitrary additive functors, including different intermediate categories.

Explicit source and target complex types now prevent repeated inference through the comparison constructors. The version with these annotations compiled in 54.9 seconds.

The public mathematical meaning and the main theorem statement are unchanged. Targets using this definition should retain their statement review with the equality above checked; the definition change is explicitly submitted for independent review.

## Old

```lean
@[irreducible] def coefficientComplexMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  (Functor.mapHomologicalComplexCompIso (sheafCoefficientIso φ j) (.up ℤ)).hom.app P ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ U ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} B) j)) (.up ℤ)).inv.app P
```

## New

```lean
@[irreducible] def coefficientComplexMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj P) ⟶
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapHomologicalComplex (.up ℤ)).obj
      (((ProEtale.etaleSheafExtendScalars φ U).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexCompIso (sheafCoefficientIso φ j) (.up ℤ)).hom.app P
```

## Users

`python3 tools/downstream.py Sheaf.Paper.EtaleOpenCounitFlatModels --uses coefficientComplexMap evaluationComplexMap` reports zero downstream modules and only this module as a textual user of either declaration. The quarantined attachment of the assigned item remains preserved; no parent or declaration is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleOpenCounitFlatModels | H1 | Model equation proofs use the equivalent direct complex map; the statement is unchanged. |

## Status

landed 20261025T050812-L-3844656 2026-10-25 (merge of deliver/H1/Sheaf.Paper.EtaleOpenCounitFlatModels)
