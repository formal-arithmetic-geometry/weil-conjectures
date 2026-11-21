/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeMateFactorization

/-! # AffineBaseChangeTildeOrdinaryComparison

## References

* Stacks Project, Tag 0DJ8
* Stacks Project, Tag 06Y6
* Stacks Project, Tag 08IB
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option linter.unusedVariables false in
/-- Ordinary affine mate calculation before extension of the source cohomology. -/
theorem exists_affineBaseChangeTildeOrdinaryComparison
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (hw : Spec.map (CommRingCat.ofHom φg') ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom φf') ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
 :
    let m := ModuleCat.baseDerivedTensorCohomologyModel R A R' M A'
    let α := algebraMap (A ⊗[R] R') A'
    let j : R' →+* A ⊗[R] R' := Algebra.TensorProduct.includeRight.toRingHom
    ∃ d : affineDerivedCohomologyModules A' i ⋙
          (ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')) ≅
        (schemeDerivedQCohProperty (Spec (.of A'))).ι ⋙
          schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf')) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i,
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let V := (affineDerivedCohomologyModules A' i).obj L
    let T := tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    let C := (((ModuleCat.extendScalars (α.comp
      (algebraMap A (A ⊗[R] R')))).mapHomologicalComplex (.up ℤ)).obj M)
    let cE := m.comparison i ≫ HomologicalComplex.homologyMap m.ordinaryToLocalized i ≫
      ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom
    let ρ := ModuleCat.restrictScalarsComp' j α φf' hφf'.symm
    let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
    let z := (HomologicalComplex.homologyFunctor (ModuleCat.{u} A') (.up ℤ) i).map
      (eqToHom (by dsimp only [C, α]; rw [hφg'] : C =
        ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M)) ≫ b.hom
    let c := (ModuleCat.restrictScalars j).map cE ≫
      ρ.inv.app (C.homology i) ≫ (ModuleCat.restrictScalars φf').map z
    ∃ eC : T.obj ((ModuleCat.restrictScalars j).obj (m.cohomology i)) ≅
        H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj K)),
      eC.hom ≫ H.map (schemeDerivedBaseChangeMap
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φf'))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom φg')) hw K) = T.map c ≫ d.hom.app L := by
  classical
  obtain ⟨d, hd⟩ := exists_affineTildePushforwardCohomologyNormalization A' R' φf' i
  obtain ⟨eC, heC⟩ := exists_affineBaseChangeTildeMateFactorization
    R A R' A' φg' φf' hφg' hφf' hw K hK M hM e hc i
  refine ⟨d, eC, ?_⟩
  let Cg := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
  let t := affineBaseChangeTildeRepresentativeIso A A' φg' K M e hc
  have ht := hd ⟨_, hL⟩ Cg t
  have hb : affineTildeRepresentativeCohomologyIso A' Cg
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K) t i =
      affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i := by
    dsimp only [affineTildeRepresentativeCohomologyIso,
      affinePushforwardRepresentativeCohomologyIso, affineBaseChangeTildeCohomologyIso]
    congr 5
    dsimp only [t, affineBaseChangeTildeRepresentativeIso, affineBaseChangeTildeComplexIso]
    congr 1
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom,
      DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
      cast_eq]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    repeat erw [Category.id_comp]
  rw [hb] at ht
  dsimp only at heC ⊢
  rw [heC]
  rw [← Category.assoc, ht]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry
