/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainMap
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVResolvedOpenRoofComparison
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVBiprodRoof

/-! # Mate comparisons for the concrete resolved row roof -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option cleanup.letToHave false
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
attribute [local instance 2000] schemeMVModuleAbelian
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh RingedSpace.moduleDirectImage

set_option maxHeartbeats 900000 in
-- The middle-vertex type contains fixed complex and derived functor comparisons.
/-- The diagonal middle component of the normalized resolved row roof has the
specified mate comparison. Source: Stacks Project, Tags 08BV, 08FE, 08HY and 0D5T. -/
theorem relativeMV_resolved_roof_middle_mate_comparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (r : schemeMVResolution X K ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K') ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (u₀ : schemeMayerVietorisComplex X U V (schemeMVResolution X K) ⟶
      schemeMayerVietorisComplex X U V
        (schemeMVResolution X ((schemeDerivedDirectImage g').obj K')))
    (hr : DerivedCategory.Q.map r = (schemeMVResolutionIso X K).hom ≫
      (relativeMVAdj g').homEquiv _ _ φ ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hs : DerivedCategory.Q.map s =
      (schemeMVDirectImageLocalization g').app (schemeMVResolution X' K') ≫
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hu₂ : u₀.τ₂ = biprod.map
      (((schemeOpenModuleImage X U).mapHomologicalComplex (.up ℤ)).map r)
      (((schemeOpenModuleImage X V).mapHomologicalComplex (.up ℤ)).map r)) :
    let I := schemeMVResolution X K
    let J := schemeMVResolution X' K'
    let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
    let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let A := (schemeMayerVietorisComplex X U V I).map Ff
    let R := (schemeMayerVietorisComplex X U V L).map Ff
    let B := (schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J).map Ff'
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    let c := (Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g hpull.w) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm).symm
    let D := schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J
    let u : A ⟶ R := Ff.mapShortComplex.map u₀
    let v : B.map F ⟶ R := (D.mapNatIso c).hom ≫
      Ff.mapShortComplex.map (schemeMVImageChainMap g' U V J L s)
    ∀ hv₂ : IsIso (DerivedCategory.Q.map v.τ₂),
      letI := hv₂
    ∃ (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₂' : DerivedCategory.Q.obj B.X₂ ≅ (b U).right ⊞ (b V).right),
      (DerivedCategory.Q.map u.τ₂ ≫ inv (DerivedCategory.Q.map v.τ₂) ≫ η.app B.X₂ =
        (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv)) := by
  classical
  extract_lets (descend := false) I J L Ff Ff' A R B G F η adj b c D u v
  intro hv₂
  have := hv₂
  let := adj.isLeftAdjoint
  let := adj.isRightAdjoint
  let : PreservesBinaryBiproducts (derivedPullback g) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  let : (derivedPullback g).Additive := Functor.additive_of_preservesBinaryBiproducts _
  let : (schemeDerivedDirectImage g).Additive := Functor.additive_of_preserves_binary_products _
  let IU := schemeOpenModuleImageComplex X U I
  let IV := schemeOpenModuleImageComplex X V I
  let LU := schemeOpenModuleImageComplex X U L
  let LV := schemeOpenModuleImageComplex X V L
  let JU := schemeOpenModuleImageComplex X' (g' ⁻¹ᵁ U) J
  let JV := schemeOpenModuleImageComplex X' (g' ⁻¹ᵁ V) J
  let H := Ff ⋙ DerivedCategory.Q
  let H' := Ff' ⋙ DerivedCategory.Q
  let T := (Ff' ⋙ F) ⋙ DerivedCategory.Q
  let G' := (RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
  let cH : T ≅ G' ⋙ H := Functor.isoWhiskerRight c DerivedCategory.Q
  let rU : IU ⟶ LU := ((schemeOpenModuleImage X U).mapHomologicalComplex (.up ℤ)).map r
  let rV : IV ⟶ LV := ((schemeOpenModuleImage X V).mapHomologicalComplex (.up ℤ)).map r
  let sU : G'.obj JU ⟶ LU := schemeMVImageComponent g' U J L s
  let sV : G'.obj JV ⟶ LV := schemeMVImageComponent g' V J L s
  let pU : H.obj IU ⟶ H.obj LU := H.map rU
  let pV : H.obj IV ⟶ H.obj LV := H.map rV
  let wU : (Ff' ⋙ F).obj JU ⟶ Ff.obj LU := c.hom.app JU ≫ Ff.map sU
  let wV : (Ff' ⋙ F).obj JV ⟶ Ff.obj LV := c.hom.app JV ≫ Ff.map sV
  let qU : T.obj JU ⟶ H.obj LU := DerivedCategory.Q.map wU
  let qV : T.obj JV ⟶ H.obj LV := DerivedCategory.Q.map wV
  let i := H.mapBiprod IU IV
  let j := H'.mapBiprod JU JV
  let z := H.mapBiprod LU LV
  let t := T.mapBiprod JU JV
  let p : H.obj (IU ⊞ IV) ⟶ H.obj (LU ⊞ LV) := DerivedCategory.Q.map u.τ₂
  let q : T.obj (JU ⊞ JV) ⟶ H.obj (LU ⊞ LV) := DerivedCategory.Q.map v.τ₂
  have : IsIso q := hv₂
  have hp : p ≫ z.hom =
      i.hom ≫ biprod.map pU pV := by
    change H.map u₀.τ₂ ≫ z.hom = _
    rw [hu₂]
    exact relativeMV_roof_numerator_pair H rU rV
  have hq : q ≫ z.hom =
      t.hom ≫ biprod.map qU qV := by
    change DerivedCategory.Q.map (c.hom.app (JU ⊞ JV) ≫
      Ff.map (biprod.lift (G'.map biprod.fst ≫ sU)
        (G'.map biprod.snd ≫ sV))) ≫ z.hom = _
    rw [Functor.map_comp]
    simpa only [qU, qV, wU, wV, cH, H, T, z, t, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.map_comp, Functor.comp_map] using
      relativeMV_roof_denominator_pair H T G' cH.hom sU sV
  have hd : biprod.map qU qV = t.inv ≫ q ≫ z.hom := by
    apply (cancel_epi t.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    exact hq.symm
  have : IsIso (biprod.map qU qV) := by rw [hd]; infer_instance
  obtain ⟨hqU, hqV⟩ := relativeMV_biprod_components_isIso qU qV
  have := hqU
  have := hqV
  have hqU' := hqU
  dsimp only [qU, wU, T, H, Ff, Ff', F, G, c, JU, J, sU, L] at hqU'
  obtain ⟨eU, eU', hU⟩ := relativeMV_resolved_open_roof_comparison
    f f' g g' hpull K K' φ U r s hr hs hqU'
  have hqV' := hqV
  dsimp only [qV, wV, T, H, Ff, Ff', F, G, c, JV, J, sV, L] at hqV'
  obtain ⟨eV, eV', hV⟩ := relativeMV_resolved_open_roof_comparison
    f f' g g' hpull K K' φ V r s hr hs hqV'
  let e₂ := (derivedPullback g).mapIso i ≪≫
    (derivedPullback g).mapBiprod (H.obj IU) (H.obj IV) ≪≫ biprod.mapIso eU eV
  let e₂' := j ≪≫ biprod.mapIso eU' eV'
  refine ⟨e₂, e₂', ?_⟩
  have ha : η.app (Ff'.obj (JU ⊞ JV)) ≫ (schemeDerivedDirectImage g).map j.hom ≫
      ((schemeDerivedDirectImage g).mapBiprod (H'.obj JU) (H'.obj JV)).hom =
        t.hom ≫ biprod.map (η.app (Ff'.obj JU)) (η.app (Ff'.obj JV)) :=
    relativeMV_roof_unit_pair T H' (schemeDerivedDirectImage g)
      (Functor.whiskerLeft Ff' η) JU JV
  have hroof := relativeMV_roof_pair (schemeDerivedDirectImage g) i j z t
    (η.app (Ff'.obj (JU ⊞ JV))) (η.app (Ff'.obj JU)) (η.app (Ff'.obj JV))
    p pU pV q qU qV hp hq ha
  have hmates := relativeMV_pair_mates adj i j eU eV eU' eV' (b U).hom (b V).hom
  change pU ≫ inv qU ≫ η.app (Ff'.obj JU) = _ at hU
  change pV ≫ inv qV ≫ η.app (Ff'.obj JV) = _ at hV
  rw [hU, hV] at hroof
  change p ≫ inv q ≫ η.app (Ff'.obj (JU ⊞ JV)) =
    adj.homEquiv (H.obj (IU ⊞ IV)) (H'.obj (JU ⊞ JV))
      (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv)
  apply (cancel_mono ((schemeDerivedDirectImage g).map j.hom ≫
    ((schemeDerivedDirectImage g).mapBiprod (H'.obj JU) (H'.obj JV)).hom)).mp
  simpa only [Category.assoc, e₂, e₂'] using hroof.trans hmates.symm

end AlgebraicGeometry
