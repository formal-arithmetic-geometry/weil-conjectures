/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVDirectImageSquareLocalization

/-! # Localization of a roof of normalized coefficient representatives -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

set_option linter.all false in
set_option maxHeartbeats 600000 in
-- Normalization compares several chosen derived functors on three representatives.
/-- A normalized coefficient roof localizes to the corresponding direct-image
square mate. Source: Stacks Project, Tags 08HY and 0D5T.
(blueprint: lem-pc-relative-mv-normalized-coefficient-roof).
Proof: Compare Q(f_*I) with Rf_*E by the inverse K-injective computation
isomorphism followed by Rf_*eI; similarly compare Q(f'_*J) with Rf'_*E'.
For L use the inverse computation map followed by Rf_*eL. Naturality of the
localization unit at r and its prescribed localization identify the numerator
with Rf_*β. Naturality at s and its prescribed localization identify the
denominator, followed by the comparison for L and the derived square mate,
with η_g(f'_*J) followed by Rg_* of the target comparison. This last identity
is the pasted complex square-unit equation, transported along eJ by naturality
of the square mate. Cancel the assumed invertible denominator and the target
comparison. Substitution gives exactly the displayed roof formula. No
Mayer--Vietoris row, cover, open, boundary or coefficient transpose occurs.
Zero β and zero objects obey the same unit naturality equations. -/
theorem relativeMV_normalized_coefficient_roof
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (E : schemeDerivedCategory X) (E' : schemeDerivedCategory X')
    (I L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ)
    [I.IsKInjective] [J.IsKInjective] [L.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ E) (eJ : DerivedCategory.Q.obj J ≅ E')
    (eL : DerivedCategory.Q.obj L ≅ (schemeDerivedDirectImage g').obj E')
    (β : E ⟶ (schemeDerivedDirectImage g').obj E')
    (r : I ⟶ L)
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj J ⟶ L)
    (hr : DerivedCategory.Q.map r = eI.hom ≫ β ≫ eL.inv)
    (hs : DerivedCategory.Q.map s = (schemeMVDirectImageLocalization g').app J ≫
      (schemeDerivedDirectImage g').map eJ.hom ≫ eL.inv) :
    let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let c := Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g h) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm
    let v := c.inv.app J ≫ Ff.map s
    ∀ hv : IsIso (DerivedCategory.Q.map v),
    letI := hv
    let κ := relativeMVComp f' g ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback.{u, w} t) h.symm) ≪≫
      (relativeMVComp g' f).symm
    let δ := conjugateEquiv ((relativeMVAdj f).comp (relativeMVAdj g'))
      ((relativeMVAdj g).comp (relativeMVAdj f')) κ.hom
    let a := (RingedSpace.derivedModuleDirectImageKInjectiveIso
        f.toLRSHom.toShHom I).symm ≪≫ (schemeDerivedDirectImage f).mapIso eI
    let b := (RingedSpace.derivedModuleDirectImageKInjectiveIso
        f'.toLRSHom.toShHom J).symm ≪≫ (schemeDerivedDirectImage f').mapIso eJ
    DerivedCategory.Q.map (Ff.map r) ≫ inv (DerivedCategory.Q.map v) ≫
        (schemeMVDirectImageLocalization g).app (Ff'.obj J) =
      a.hom ≫ (schemeDerivedDirectImage f).map β ≫ δ.app E' ≫
        (schemeDerivedDirectImage g).map b.inv := by
  classical
  extract_lets (descend := false) Ff Ff' c v
  intro hv
  have := hv
  extract_lets (descend := false) κ δ a b
  let d := (RingedSpace.derivedModuleDirectImageKInjectiveIso
    f.toLRSHom.toShHom L).symm ≪≫ (schemeDerivedDirectImage f).mapIso eL
  have hnr : DerivedCategory.Q.map r ≫ eL.hom = eI.hom ≫ β := by
    rw [hr]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hns : DerivedCategory.Q.map s ≫ eL.hom =
      (schemeMVDirectImageLocalization g').app J ≫
        (schemeDerivedDirectImage g').map eJ.hom := by
    rw [hs]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := (schemeMVDirectImageLocalization f).naturality r
  dsimp only [Functor.comp_map] at hn
  have hu : DerivedCategory.Q.map (Ff.map r) ≫ d.hom =
      a.hom ≫ (schemeDerivedDirectImage f).map β := by
    dsimp only [d, a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← schemeMVDirectImageLocalization_app f L,
      ← schemeMVDirectImageLocalization_app f I]
    rw [← Category.assoc, hn, Category.assoc,
      ← Functor.map_comp, hnr, Functor.map_comp, Category.assoc]
  have hn := (schemeMVDirectImageLocalization f).naturality s
  dsimp only [Functor.comp_map] at hn
  have hfs : DerivedCategory.Q.map (Ff.map s) ≫
      (schemeMVDirectImageLocalization f).app L ≫
      (schemeDerivedDirectImage f).map eL.hom =
    (schemeMVDirectImageLocalization f).app
        (((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage f).map ((schemeMVDirectImageLocalization g').app J) ≫
      (schemeDerivedDirectImage f).map ((schemeDerivedDirectImage g').map eJ.hom) := by
    rw [← Category.assoc, hn, Category.assoc,
      ← Functor.map_comp, hns, Functor.map_comp]
  have hd := δ.naturality eJ.hom
  dsimp only [Functor.comp_map] at hd
  have hunit := relativeMV_direct_image_square_localization f f' g g' h J
  have hvn : DerivedCategory.Q.map v ≫ d.hom ≫ δ.app E' =
      (schemeMVDirectImageLocalization g).app (Ff'.obj J) ≫
        (schemeDerivedDirectImage g).map b.hom := by
    calc
      _ = DerivedCategory.Q.map (c.inv.app J) ≫
          (schemeMVDirectImageLocalization f).app
            (((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
              (.up ℤ)).obj J) ≫
          (schemeDerivedDirectImage f).map ((schemeMVDirectImageLocalization g').app J) ≫
          (schemeDerivedDirectImage f).map ((schemeDerivedDirectImage g').map eJ.hom) ≫
          δ.app E' := by
        dsimp only [v, d, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
        rw [DerivedCategory.Q.map_comp, ← schemeMVDirectImageLocalization_app f L]
        simpa only [Category.assoc] using
          congrArg (fun t ↦ DerivedCategory.Q.map (c.inv.app J) ≫ t ≫ δ.app E') hfs
      _ = DerivedCategory.Q.map (c.inv.app J) ≫
          (schemeMVDirectImageLocalization f).app
            (((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
              (.up ℤ)).obj J) ≫
          (schemeDerivedDirectImage f).map ((schemeMVDirectImageLocalization g').app J) ≫
          δ.app (DerivedCategory.Q.obj J) ≫
          (schemeDerivedDirectImage g).map ((schemeDerivedDirectImage f').map eJ.hom) := by
        rw [hd]
      _ = DerivedCategory.Q.map (c.inv.app J) ≫ DerivedCategory.Q.map (c.hom.app J) ≫
          (schemeMVDirectImageLocalization g).app (Ff'.obj J) ≫
          (schemeDerivedDirectImage g).map ((schemeMVDirectImageLocalization f').app J) ≫
          (schemeDerivedDirectImage g).map ((schemeDerivedDirectImage f').map eJ.hom) := by
        simpa only [Category.assoc] using congrArg (fun t ↦
          DerivedCategory.Q.map (c.inv.app J) ≫ t ≫
            (schemeDerivedDirectImage g).map ((schemeDerivedDirectImage f').map eJ.hom))
          hunit
      _ = _ := by
        rw [← DerivedCategory.Q.map_comp_assoc, Iso.inv_hom_id_app,
          DerivedCategory.Q.map_id, Category.id_comp, ← Functor.map_comp]
        dsimp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
        rw [schemeMVDirectImageLocalization_app f' J]
  have hvinv : inv (DerivedCategory.Q.map v) ≫
      (schemeMVDirectImageLocalization g).app (Ff'.obj J) =
      d.hom ≫ δ.app E' ≫ (schemeDerivedDirectImage g).map b.inv := by
    apply (cancel_epi (DerivedCategory.Q.map v)).mp
    simp only [IsIso.hom_inv_id_assoc]
    have he := congrArg (fun t ↦ t ≫ (schemeDerivedDirectImage g).map b.inv) hvn
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id] at he
    rw [(schemeDerivedDirectImage g).map_id] at he
    exact (Category.comp_id _).symm.trans he.symm
  rw [hvinv]
  simpa only [Category.assoc] using congrArg (fun t ↦
    t ≫ δ.app E' ≫ (schemeDerivedDirectImage g).map b.inv) hu

end AlgebraicGeometry
