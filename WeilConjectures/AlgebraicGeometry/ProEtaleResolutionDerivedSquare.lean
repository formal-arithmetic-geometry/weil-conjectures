/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleResolutionSigmaNaturality
import WeilConjectures.AlgebraicGeometry.ProEtaleResolutionRepresentativeSquare

/-! # The derived coefficient square by naturality and cancellation

(blueprint: lem-sp-resolution-derived-square)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] proEtaleTensorPullbackTotal proEtaleTensorPullbackTotalIso
  proEtaleRingDerivedPullbackFactors CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
  HomologicalComplex₂.total
private theorem resolutionSquare_cancel
    {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {T U A B : C} {FT FU TX UX AX BX : D}
    (eY : T ≅ U) (eX : TX ≅ UX)
    (εT : L.obj T ⟶ FT) (εU : L.obj U ⟶ FU) (w : FT ⟶ FU)
    (sT : FT ⟶ TX) (sU : FU ⟶ UX)
    (rY : T ⟶ A) (rX : TX ⟶ AX) (tY : A ⟶ B) (tX : AX ⟶ BX)
    (kH : L.obj A ⟶ AX) (kM : L.obj B ⟶ BX)
    (he : L.map eY.hom ≫ εU = εT ≫ w)
    (hsq : sT ≫ eX.hom = w ≫ sU)
    (htop : L.map rY ≫ kH = εT ≫ sT ≫ rX)
    (hnat : kH ≫ tX = L.map tY ≫ kM) :
    εU ≫ sU ≫ eX.inv ≫ rX ≫ tX = L.map (eY.inv ≫ rY ≫ tY) ≫ kM := by
  have hcan : L.map eY.hom ≫ L.map (eY.inv ≫ rY ≫ tY) =
      L.map rY ≫ L.map tY := by
    rw [← L.map_comp, eY.hom_inv_id_assoc, L.map_comp]
  apply (cancel_epi (L.map eY.hom)).1
  calc
    L.map eY.hom ≫ (εU ≫ sU ≫ eX.inv ≫ rX ≫ tX) =
        εT ≫ w ≫ sU ≫ eX.inv ≫ rX ≫ tX := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ sU ≫ eX.inv ≫ rX ≫ tX) he
    _ = εT ≫ sT ≫ eX.hom ≫ eX.inv ≫ rX ≫ tX := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ εT ≫ z ≫ eX.inv ≫ rX ≫ tX) hsq.symm
    _ = εT ≫ sT ≫ rX ≫ tX := by rw [eX.hom_inv_id_assoc]
    _ = L.map rY ≫ kH ≫ tX := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ tX) htop.symm
    _ = L.map rY ≫ L.map tY ≫ kM := by rw [hnat]
    _ = L.map eY.hom ≫ (L.map (eY.inv ≫ rY ≫ tY) ≫ kM) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ kM) hcan.symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- Localizing the coefficient square gives the specified derived identity.
Source: Stacks Project, Cohomology on Sites, Tag 07A4.
Proof: cancel L(eY.hom), use epsilon naturality and the chain square to cancel eX,
substitute the representative square, and move the coefficient map across tau by
naturality and bifunctoriality. Finally cancel eY.
(blueprint: lem-sp-resolution-derived-square). -/
theorem proEtale_resolution_derived_square
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (P H M : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hP : proEtaleFlatRepresentatives Y R P)
    (hH : proEtaleFlatRepresentatives Y R H)
    (hFP : proEtaleFlatRepresentatives X S ((((proEtaleRingModulePullback f R S
        c).mapHomologicalComplex (.up ℤ))).obj P))
    (hFH : proEtaleFlatRepresentatives X S ((((proEtaleRingModulePullback f R S
        c).mapHomologicalComplex (.up ℤ))).obj H))
    (q : H ⟶ M)
    (eY : DerivedCategory.Q.obj (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y
        R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, H)) ≅
      DerivedCategory.Q.obj (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y
          R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, M)))
    (eX : DerivedCategory.Q.obj (((Functor.uncurry.obj ((proEtaleOrdinaryTensor X
        S).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj
        ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj P,
          (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj H)) ≅
      DerivedCategory.Q.obj (((Functor.uncurry.obj ((proEtaleOrdinaryTensor X
          S).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj
        ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj P,
          (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj M)))
    (heY : eY.hom = DerivedCategory.Q.map (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y
        R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))).map (Prod.mkHom (𝟙 P) q))))
    (heX : eX.hom = DerivedCategory.Q.map (((Functor.uncurry.obj ((proEtaleOrdinaryTensor X
        S).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))).map (Prod.mkHom
      (𝟙 ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj P))
      ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).map q))))) :
        (proEtaleRingDerivedPullbackFactors f R S c).hom.app
            (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, M)) ≫
          DerivedCategory.Q.map
            ((proEtaleTensorPullbackTotalIso f R S c P M).symm).hom ≫
          (eX.inv ≫ b.representative.hom.app
            (⟨(((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj P, hFP⟩,
              ⟨(((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj H, hFH⟩) ≫
            b.tensor.map (Prod.mkHom
              (𝟙 (DerivedCategory.Q.obj ((((proEtaleRingModulePullback f R S
                  c).mapHomologicalComplex (.up ℤ))).obj P)))
              (DerivedCategory.Q.map ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex
                  (.up ℤ))).map q)))) =
        (proEtaleRingDerivedPullback f R S c).map
            (eY.inv ≫ a.representative.hom.app (⟨P, hP⟩, ⟨H, hH⟩) ≫
              a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
                (DerivedCategory.Q.map q))) ≫
          (proEtaleCanonicalTensorComparison f R S c a b).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (M)) ≫
          b.tensor.map (Prod.mkHom
            ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
            ((proEtaleRingDerivedPullbackFactors f R S c).hom.app
              (M))) := by
  classical
  let F := ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))
  let L := proEtaleRingDerivedPullback f R S c
  let ε := (proEtaleRingDerivedPullbackFactors f R S c).hom
  let τ := (proEtaleCanonicalTensorComparison f R S c a b).hom
  let u := ((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))).map (Prod.mkHom (𝟙 P) q))
  have hsq := proEtale_resolution_sigma_naturality f R S c P H M q
  have htop := proEtale_resolution_representative_square f R S c a b P H hP hH hFP hFH
  let rY : DerivedCategory.Q.obj (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y
      R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, H)) ⟶
      a.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj H) :=
    a.representative.hom.app (⟨P, hP⟩, ⟨H, hH⟩)
  let rX : DerivedCategory.Q.obj
      (((Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (F.obj P, F.obj H)) ⟶
      b.tensor.obj (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj (F.obj H)) :=
    b.representative.hom.app (⟨F.obj P, hFP⟩, ⟨F.obj H, hFH⟩)
  let sH : F.obj (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, H)) ⟶
      ((Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (F.obj P, F.obj H) :=
    ((proEtaleTensorPullbackTotalIso f R S c P H).symm).hom
  let sM : F.obj (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, M)) ⟶
      ((Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (F.obj P, F.obj M) :=
    ((proEtaleTensorPullbackTotalIso f R S c P M).symm).hom
  let tY := a.tensor.map
    (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q))
  let tX := b.tensor.map
    (Prod.mkHom (𝟙 (DerivedCategory.Q.obj (F.obj P))) (DerivedCategory.Q.map (F.map q)))
  change ε.app (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, M)) ≫
      DerivedCategory.Q.map sM ≫ (eX.inv ≫ rX ≫ tX) =
    L.map (eY.inv ≫ rY ≫ tY) ≫
      τ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj M) ≫
        b.tensor.map (Prod.mkHom (ε.app P) (ε.app M))
  have heq : b.tensor.map (Prod.mkHom (ε.app P) (ε.app H)) ≫ tX =
      b.tensor.map (Prod.mkHom (L.map (𝟙 (DerivedCategory.Q.obj P)))
        (L.map (DerivedCategory.Q.map q))) ≫
          b.tensor.map (Prod.mkHom (ε.app P) (ε.app M)) := by
    rw [← b.tensor.map_comp, ← b.tensor.map_comp]
    congr 1
    apply Prod.ext
    · change ε.app P ≫ 𝟙 _ = L.map (𝟙 _) ≫ ε.app P
      rw [L.map_id, Category.id_comp, Category.comp_id]
    · exact (ε.naturality q).symm
  have hn := τ.naturality
    (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q))
  change L.map tY ≫ τ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj M) =
    τ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj H) ≫
      b.tensor.map (Prod.mkHom (L.map (𝟙 (DerivedCategory.Q.obj P)))
        (L.map (DerivedCategory.Q.map q))) at hn
  have heu := ε.naturality u
  dsimp only [Functor.comp_map] at heu
  rw [← heY] at heu
  change L.map eY.hom ≫ ε.app (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y
      R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, M)) =
    ε.app (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, H)) ≫
      DerivedCategory.Q.map (F.map u) at heu
  have hloc := congrArg DerivedCategory.Q.map hsq
  rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, ← heX] at hloc
  change DerivedCategory.Q.map sH ≫ eX.hom =
    DerivedCategory.Q.map (F.map u) ≫ DerivedCategory.Q.map sM at hloc
  apply resolutionSquare_cancel L eY eX
    (ε.app (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, H)))
    (ε.app (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, M)))
    (DerivedCategory.Q.map (F.map u)) (DerivedCategory.Q.map sH)
    (DerivedCategory.Q.map sM) rY rX tY tX
    (τ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj H) ≫
      b.tensor.map (Prod.mkHom (ε.app P) (ε.app H)))
    (τ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj M) ≫
      b.tensor.map (Prod.mkHom (ε.app P) (ε.app M))) heu hloc htop
  rw [Category.assoc, heq]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ b.tensor.map (Prod.mkHom (ε.app P) (ε.app M))) hn.symm
end AlgebraicGeometry.Scheme
