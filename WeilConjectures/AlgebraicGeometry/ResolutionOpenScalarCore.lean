/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ResolutionOpenComparisonMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ResolutionSectionsHomologyScalar
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.Linear

/-! # The fixed comparison intertwines the scalar endomorphisms.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

set_option maxHeartbeats 800000 in
-- Comparing the two exact homology calculations needs additional elaboration.
/-- The fixed comparison intertwines the scalar endomorphisms. -/
theorem resolution_open_scalar_core {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (a : Γ(T, W))
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let : CommRing (Y.ringCatSheaf.obj.obj (op ⊤)) :=
    inferInstanceAs (CommRing Γ(Y, ⊤))
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let c := resolutionOpenComparison f F I q W R
    ∀ (n : ℕ) (x : P.obj (op W)),
      (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
        (G.smulHom (b ^ n)) (c x) = c (a ^ n • x) := by
  dsimp only
  intro n x
  let Y := (f ⁻¹ᵁ W).toScheme
  let : CommRing (Y.ringCatSheaf.obj.obj (op ⊤)) :=
    inferInstanceAs (CommRing Γ(Y, ⊤))
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
  let K := ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let A := RingedSpace.globalSectionsComplex R.resolution
  let B := ((SheafOfModules.forget T.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj K
  let Q := forget₂ (ModuleCat.{u} (Y.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}
  let E := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
    (evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) q
  let eA := (A.sc q).mapHomologyIso Q
  let eB := (B.sc q).mapHomologyIso E
  let S := RingedSpace.openModuleSections Y.toRingedSpace ⊤
  let : S.Additive := RingedSpace.openModuleSections_additive Y.toRingedSpace ⊤
  let eR := R.resolution.isoRightDerivedObj S q
  let raw := H.map R.sections.hom ≫ eB.hom
  let phi : R.resolution.cocomplex ⟶ R.resolution.cocomplex :=
    { f := fun i ↦ (R.resolution.cocomplex.X i).smulHom (b ^ n)
      comm' := fun i j _ ↦ smulHom_naturality (R.resolution.cocomplex.d i j) (b ^ n) }
  have hphi : R.resolution.ι.f 0 ≫ phi.f 0 =
      G.smulHom (b ^ n) ≫ R.resolution.ι.f 0 :=
    (smulHom_naturality (R.resolution.ι.f 0) (b ^ n)).symm
  have hnat := R.resolution.isoRightDerivedObj_hom_naturality
    (G.smulHom (b ^ n)) R.resolution phi hphi S q
  have ht (y : A.homology q) :
      (eA.inv ≫ raw) ((b ^ n) • y) = a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from
        (eA.inv ≫ raw) y) := by
    have hs := resolutionSectionsHomology_scalar f F I q W R (a ^ n) y
    let h := f.resLE W (f ⁻¹ᵁ W) le_rfl ≫ W.toSpecΓ
    have hb : (Scheme.ΓSpecIso Γ(T, W)).inv ≫ h.appTop ≫
        (f ⁻¹ᵁ W).topIso.hom = f.app W := by
      simp only [h, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
        Category.assoc, Iso.inv_hom_id_assoc, Scheme.Hom.appTop,
        Scheme.Hom.resLE_app_top, Iso.inv_hom_id,
        Category.comp_id, Scheme.Hom.appLE]
      simp only [homOfLE_refl, op_id]
      rw [X.presheaf.map_id, Category.comp_id]
    have hb' : (Scheme.ΓSpecIso Γ(T, W)).inv ≫ h.appTop =
        f.app W ≫ (f ⁻¹ᵁ W).topIso.inv := by
      rw [← hb]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change (eA.inv ≫ raw) ((((Scheme.ΓSpecIso Γ(T, W)).inv ≫ h.appTop).hom
      (a ^ n)) • y) = a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from
        (eA.inv ≫ raw) y) at hs
    rw [hb', map_pow] at hs
    exact hs
  have hh (y : (H.obj ((S.mapHomologicalComplex (.up ℕ)).obj
      R.resolution.cocomplex))) :
      raw ((S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi y) =
        a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from raw y) := by
    let GS := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    let : GS.Additive := RingedSpace.globalSectionsFunctor_additive Y.toRingedSpace
    let phiA := (GS.mapHomologicalComplex (.up ℕ)).map phi
    have hphiA : phiA = (show Y.ringCatSheaf.obj.obj (op ⊤) from b ^ n) • 𝟙 A := by
      ext i z
      exact smulHom_app_top_apply (R.resolution.cocomplex.X i) (b ^ n) z
    have hphiH : (HomologicalComplex.homologyFunctor
        (ModuleCat (Y.ringCatSheaf.obj.obj (op ⊤))) (.up ℕ) q).map phiA =
        (show Y.ringCatSheaf.obj.obj (op ⊤) from b ^ n) • 𝟙 _ := by
      rw [hphiA]
      change ShortComplex.homologyMap _ = _
      have hsc : (HomologicalComplex.shortComplexFunctor
          (ModuleCat (Y.ringCatSheaf.obj.obj (op ⊤))) (.up ℕ) q).map
          ((show Y.ringCatSheaf.obj.obj (op ⊤) from b ^ n) • 𝟙 A) =
          (show Y.ringCatSheaf.obj.obj (op ⊤) from b ^ n) • 𝟙 (A.sc q) := by
        ext <;> rfl
      rw [hsc, ShortComplex.homologyMap_smul]
      erw [ShortComplex.homologyMap_id]
      rfl
    have hhA := ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map phiA) Q
    change (S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi ≫ eA.hom =
      eA.hom ≫ Q.map
        ((HomologicalComplex.homologyFunctor _ (.up ℕ) q).map phiA) at hhA
    rw [hphiH] at hhA
    have hy := ConcreteCategory.congr_hom hhA y
    change eA.hom ((S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi y) =
      (b ^ n) • (show A.homology q from eA.hom y) at hy
    calc
      raw ((S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi y) =
          (eA.inv ≫ raw) (eA.hom ((S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi y)) := by
            simp
            rfl
      _ = a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from
          (eA.inv ≫ raw) (eA.hom y)) := by rw [hy, ht]
      _ = a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from raw y) := by
        simp
        rfl
  have hc (z : (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj G) :
      (eR.hom ≫ raw) ((RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
        (G.smulHom (b ^ n)) z) = a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from
        (eR.hom ≫ raw) z) := by
    have hz := ConcreteCategory.congr_hom hnat z
    change eR.hom ((RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
      (G.smulHom (b ^ n)) z) = (S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi
        (eR.hom z) at hz
    change raw (eR.hom _) = _
    erw [hz]
    exact hh _
  apply (resolutionOpenComparison f F I q W R).symm.injective
  simp only [AddEquiv.symm_apply_apply]
  change (eR.hom ≫ raw) _ = a ^ n • x
  rw [hc]
  change a ^ n • ((resolutionOpenComparison f F I q W R).symm
    ((resolutionOpenComparison f F I q W R) x)) = _
  simp only [AddEquiv.symm_apply_apply]


end AlgebraicGeometry.Scheme.Modules
