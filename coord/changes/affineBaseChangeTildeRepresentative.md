# AlgebraicGeometry.affineBaseChangeTildeRepresentativeIso

## Reason

Expose the existing complex comparison and prove its identity-representative counit cancellation. The module is unclaimed; no other holder is adapted.

## Old

```lean
def affineBaseChangeTildeRepresentativeIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    DerivedCategory.Q.obj (((affineTildeFunctor A').mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≅
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K := by
  let TA := affineTildeFunctor A
  let TB := affineTildeFunctor A'
  let : TA.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : TB.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let f := Spec.map (CommRingCat.ofHom φ)
  let P := (TA.mapHomologicalComplex (.up ℤ)).obj M
  let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f
  let : IsIso ((SingleComplexBaseChange.counit f).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hc
  let θ := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom φ))
  let θ' : TA ⋙ E ≅ ModuleCat.extendScalars φ ⋙ TB := θ
  let δ : (E.mapHomologicalComplex (.up ℤ)).obj P ≅
      (TB.mapHomologicalComplex (.up ℤ)).obj C :=
    (Functor.mapHomologicalComplexCompIso θ' (.up ℤ)).app M
  exact (DerivedCategory.Q.mapIso δ).symm ≪≫
    (asIso ((SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))).symm ≪≫
    (derivedPullback f).mapIso e
```

## New

```lean
def affineBaseChangeTildeRepresentativeIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    DerivedCategory.Q.obj (((affineTildeFunctor A').mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≅
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let P := ((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M
  let : IsIso ((SingleComplexBaseChange.counit f).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hc
  let δ := affineBaseChangeTildeComplexIso A A' φ M
  exact (DerivedCategory.Q.mapIso δ).symm ≪≫
    (asIso ((SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))).symm ≪≫
    (derivedPullback f).mapIso e
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.AffineBaseChangeTildeMateFactorization` | unclaimed | Definitionally identical construction; unchanged |
| `Sheaf.Algebra.Homology.AffineBaseChangeTildeMateIdentityFactorization` | unclaimed | Definitionally identical construction; unchanged |
| `Sheaf.Algebra.Homology.AffineBaseChangeTildeOrdinaryComparison` | unclaimed | Definitionally identical construction; unchanged |
| `Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate` | unclaimed | Definitionally identical construction; unchanged |
| `Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange` | P1 | Uses proved cancellation |
| `Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization` | new, P1 | Uses the explicit complex comparison |

## Status

landed 20261014T204310-L-2517264 2026-10-14 (merge of deliver/P1/Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange)
