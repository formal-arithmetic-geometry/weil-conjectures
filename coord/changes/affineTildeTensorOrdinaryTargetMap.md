# AlgebraicGeometry.affineTildeTensorOrdinaryTargetMap

## Reason

Share the actual degreewise affine pushforward map. It has the same components as the original mapHomologicalComplex construction. The parent theorem uses the new lower transport and proved counit cancellation. The original local additive instance is preserved and three redundant direct proof imports are removed. The new public import is needed by this public definition, whose body uses affineTildePushforwardComplexMap.

## Old

```lean
def affineTildeTensorOrdinaryTargetMap
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (φ : A →+* D) (ψ : B →+* D)
    (k : (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ⟶
      ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) :
    DerivedCategory.Q.{w}.obj (((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M))) ⟶
    (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom ψ))).obj
      (DerivedCategory.Q.{w}.obj (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))) := by
  let T := affineTildeFunctor B
  let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let σ := affineTildePushforwardComparison D B ψ
  let F := ModuleCat.restrictScalars ψ ⋙ T
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))
  let : (affineTildeFunctor D).Additive :=
    instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : P.Additive := inferInstance
  let : (affineTildeFunctor D ⋙ P).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by
      rw [Functor.comp_map, (affineTildeFunctor D).map_zero]
      exact P.map_zero _ _⟩
  let a : (F.mapHomologicalComplex (.up ℤ)).obj Cg ⟶
      (P.mapHomologicalComplex (.up ℤ)).obj
        (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj Cg) :=
    (σ.hom.mapHomologicalComplex (.up ℤ)).app Cg
  exact DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map k) ≫
    DerivedCategory.Q.map a ≫
    (RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj Cg))
```

## New

```lean
def affineTildeTensorOrdinaryTargetMap
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (φ : A →+* D) (ψ : B →+* D)
    (k : (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ⟶
      ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) :
    DerivedCategory.Q.{w}.obj (((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M))) ⟶
    (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom ψ))).obj
      (DerivedCategory.Q.{w}.obj (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))) := by
  let T := affineTildeFunctor B
  let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let a := affineTildePushforwardComplexMap D B ψ Cg
  exact DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map k) ≫
    DerivedCategory.Q.map a ≫
    (RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj Cg))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate` | unclaimed | Definitionally identical target map; unchanged |
| `Sheaf.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates` | unclaimed | Definitionally identical target map; unchanged |
| `Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization` | new, P1 | Shares the chain map; does not import the parent |

## Status

landed 20261014T204310-L-2517264 2026-10-14 (merge of deliver/P1/Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange)
