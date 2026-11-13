/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.OpenRestrictionModuleCohomology
import WeilConjectures.AlgebraicGeometry.HigherDirectImageResolutionNaturality

/-! # Coefficient-natural comparison with resolution section cohomology

## References

* Stacks Project, Cohomology, Tags 01E1 and 01E4.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Scheme.Modules.enoughInjectives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

private def derivedSectionsMap {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) (V : Y.Opens) :
    (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).rightDerived p ⟶
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
        RingedSpace.openModuleSections Y.toRingedSpace V where
  app N := higherDirectImageResolutionSectionMap f p V (injectiveResolution N)
  naturality := fun _ _ a ↦ higherDirectImage_resolution_naturality f p V a _ _

private theorem derivedSectionsMap_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : ℕ) (V : Y.Opens)
    {N : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (I : InjectiveResolution N) :
    (derivedSectionsMap f p V).app N = higherDirectImageResolutionSectionMap f p V I := by
  have h :
      ((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).rightDerived p).map
          (𝟙 N) ≫ higherDirectImageResolutionSectionMap f p V I =
        higherDirectImageResolutionSectionMap f p V (injectiveResolution N) ≫
          ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
            RingedSpace.openModuleSections Y.toRingedSpace V).map (𝟙 N) :=
    higherDirectImage_resolution_naturality f p V (𝟙 N) (injectiveResolution N) I
  have hT := (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).rightDerived p
    |>.map_id N
  have hD := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
    RingedSpace.openModuleSections Y.toRingedSpace V).map_id N
  erw [hT, hD] at h
  exact ((Category.comp_id
    (higherDirectImageResolutionSectionMap f p V (injectiveResolution N))).symm.trans
    (h.symm.trans (Category.id_comp (higherDirectImageResolutionSectionMap f p V I))))

/-- The comparison from cohomology on inverse-image opens to higher-image sections
is natural in coefficients. Its component is the resolution comparison followed by
the canonical map `theta`. This asserts no detection of morphisms on an affine basis
(Stacks, Tags 01E1 and 01E4). -/
theorem higherDirectImage_coefficient_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) :
    ∃ c : ∀ V : Y.Opens,
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
              AddCommGrpCat.{u} ⟶
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
        RingedSpace.openModuleSections Y.toRingedSpace V,
      ∀ (N : X.Modules) (I : InjectiveResolution
        (show SheafOfModules.{u} (moduleRings X.toRingedSpace) from N)) (V : Y.Opens),
        let K := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex
        ∃ e :
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
            RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p ⋙
              forget₂ (ModuleCat.{u}
                ((moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
                  AddCommGrpCat.{u}).obj N) ≅
            (Scheme.Modules.sectionCohomologyPresheaf K p).presheaf.obj (Opposite.op V),
          (c V).app N = e.hom ≫
            ((PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj).map
              (Scheme.Modules.sectionCohomologyTheta K p ≫
                (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
                  (I.isoRightDerivedObj
                    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv)).app
                      (Opposite.op V) := by
  classical
  let a (V : Y.Opens) := Classical.choice
    (nonempty_openRestriction_moduleCohomology_iso X (f ⁻¹ᵁ V) p)
  refine ⟨fun V ↦ (a V).hom ≫ derivedSectionsMap f p V, ?_⟩
  intro N I V
  let K : CochainComplex Y.Modules ℕ :=
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex
  let L := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj K
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
    (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V)
  let e := (a V).app N ≪≫
    I.isoRightDerivedObj (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)) p ≪≫
      (L.sc p).mapHomologyIso E
  refine ⟨e, ?_⟩
  dsimp only [NatTrans.comp_app]
  rw [derivedSectionsMap_app f p V I]
  simp only [e, higherDirectImageResolutionSectionMap, Iso.trans_hom, Category.assoc]
  rfl

end

end AlgebraicGeometry
