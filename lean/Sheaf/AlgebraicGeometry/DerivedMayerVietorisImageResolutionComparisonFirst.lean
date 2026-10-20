module
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle
import Sheaf.AlgebraicGeometry.MayerVietorisDirectImageChainSquares
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

private theorem resolution_map_surjective
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (I J : CochainComplex A ℤ) [J.IsKInjective]
    (φ : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    ∃ f : I ⟶ J, DerivedCategory.Q.map f = φ := by
  let e := DerivedCategory.quotientCompQhIso A
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj I) J).surjective
      (e.hom.app I ≫ φ ≫ e.inv.app J)
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  refine ⟨f, ?_⟩
  have hn := e.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hf, hg] at hn
  apply (cancel_epi (e.hom.app I)).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hn.symm

/-- First component of the direct-image Mayer–Vietoris comparison.
(blueprint: lem-pc-mayer-vietoris-image-resolution-comparison-first)
The comparison is obtained by transporting fixed K-injective resolutions and
representing the localized direct-image map by a concrete chain map. -/
theorem schemeMV_image_resolution_comparison_first
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    [(schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))
      (schemeMVResolution X E)).IsKInjective] :
    let I := schemeMVResolution X E
    let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
    let S := schemeMayerVietorisComplex X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I
    let T := schemeMayerVietorisComplex Y U V J
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ m : S.map F ⟶ T,
      (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I).hom ≫
          DerivedCategory.Q.map m.τ₁ ≫
          (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom =
        (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom := by
  classical
  let I := schemeMVResolution X E
  let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
  let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  let eI := RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I
  let eJ := schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)
  let φ : DerivedCategory.Q.obj (F.obj I) ⟶ DerivedCategory.Q.obj J :=
    eI.inv ≫ (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom ≫ eJ.inv
  obtain ⟨f, hf⟩ := resolution_map_surjective (F.obj I) J φ
  obtain ⟨a, b, c, ha, hb, hc, hd⟩ := schemeMV_directImage_chain_squares X Y h U V I J f
  let eB := F.mapBiprod
    (schemeOpenModuleImageComplex X (h ⁻¹ᵁ U) I)
    (schemeOpenModuleImageComplex X (h ⁻¹ᵁ V) I)
  let m₂ := eB.hom ≫ biprod.map a b
  let m : (schemeMayerVietorisComplex X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I).map F ⟶
      schemeMayerVietorisComplex Y U V J :=
    ⟨f, m₂, c, by
      change f ≫ schemeMayerVietorisF Y U V J =
        F.map (schemeMayerVietorisF X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I) ≫ m₂
      dsimp only [schemeMayerVietorisF, m₂, eB]
      rw [← Category.assoc, biprod.map_lift_mapBiprod]
      apply biprod.hom_ext
      · simpa only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
          biprod.lift_fst] using ha
      · simpa only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
          biprod.lift_snd] using hb,
    by
      change m₂ ≫ schemeMayerVietorisG Y U V J =
        F.map (schemeMayerVietorisG X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I) ≫ c
      dsimp only [schemeMayerVietorisG, m₂, eB]
      rw [← biprod.mapBiprod_hom_desc]
      simp only [Category.assoc]
      apply congrArg (fun k ↦ (F.mapBiprod
        (schemeOpenModuleImageComplex X (h ⁻¹ᵁ U) I)
        (schemeOpenModuleImageComplex X (h ⁻¹ᵁ V) I)).hom ≫ k)
      apply biprod.hom_ext'
      · simpa only [biprod.inl_map_assoc, biprod.inl_desc_assoc,
          biprod.inl_desc, Category.assoc] using hc
      · simpa only [biprod.inr_map_assoc, biprod.inr_desc_assoc,
          biprod.inr_desc, Category.assoc, Functor.map_neg, Preadditive.comp_neg,
          Preadditive.neg_comp] using congrArg Neg.neg hd⟩
  refine ⟨m, ?_⟩
  change eI.hom ≫ DerivedCategory.Q.map f ≫ eJ.hom = _
  rw [hf]
  simp only [φ, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc]
end AlgebraicGeometry
