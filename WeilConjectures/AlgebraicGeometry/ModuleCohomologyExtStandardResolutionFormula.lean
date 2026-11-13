/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyStandardSectionsFactorization
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtSectionsFactorization

/-! # The fixed comparison on the chosen standard resolution

## References

* [Stacks, Tags 015E and 03FD]
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

-- Elaborating the fixed-resolution interfaces requires several derived-functor instances.
/-- Computation of the fixed comparison on Mathlib's standard injective resolution, with no
change-of-resolution assertion (Stacks, Tags 015E and 03FD). -/
theorem standard_resolution_formula
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : InjectiveResolution F) (hI : I = injectiveResolution F)
    (hι : QuasiIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)) (.up ℕ) 0).inv.app F ≫
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapHomologicalComplex
          (.up ℕ)).map I.ι)) (p : ℕ)
    (a : (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) ≅
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology p)
    (b : AddCommGrpCat.of (H F p) ≅
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology p)
    (ha : a = (forget₂ _ AddCommGrpCat.{u}).mapIso
      (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p) ≪≫
        (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
          (forget₂ _ AddCommGrpCat.{u})).symm)
    (hb : b = (by
      let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
      let ι := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app F ≫
        (T.mapHomologicalComplex (.up ℕ)).map I.ι
      haveI : QuasiIso ι := hι
      exact (Abelian.Ext.precompAddEquiv (terminalSourceIso X) (T.obj F) p).toAddCommGrpIso ≪≫
        siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ (T.obj F) p ≪≫
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
          (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).rightDerivedObjIsoOfResolution ι
            (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p))
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    moduleCohomologyExtResolutionEquiv X F p x = b.inv (a.hom x) := by
  rw [ext_sections_factorization X F p x, hb]
  simp only [Iso.trans_inv, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
    AddEquiv.toAddCommGrpIso_inv, AddCommGrpCat.hom_ofHom, AddEquiv.toAddMonoidHom_eq_coe]
  apply congrArg (fun z ↦ (Abelian.Ext.precompAddEquiv (terminalSourceIso X)
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p).symm z)
  apply congrArg (fun z ↦ (siteSectionsObjIso (Opens.grothendieckTopology X) ⊤
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p).inv z)
  exact standard_sections_factorization X F I hI hι p a ha x

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
