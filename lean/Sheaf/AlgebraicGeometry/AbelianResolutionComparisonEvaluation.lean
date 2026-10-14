/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation
import Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural

/-! # Evaluation of the target acyclic-resolution comparison

Source: Stacks Project, Tags 03FD, 015E and 06XR.
(blueprint: new-abelian-resolution-comparison-evaluation)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
attribute [local instance] AlgebraicGeometry.Scheme.Modules.instAddCommGroupH
attribute [local irreducible] abelianResolutionIso
attribute [local irreducible] Functor.rightDerivedObjIsoOfResolution
attribute [local irreducible] siteSectionsObjIso

/-- Changing from a forgotten module resolution to an abelian injective resolution.
Source: Stacks Project, Tags 03FD, 015E and 06XR.
(blueprint: new-abelian-resolution-comparison-evaluation)

Proof: The forgotten terms are section-acyclic by 03FD. The augmentation square
makes phi a comparison of the two resolutions of the same underlying sheaf.
Apply naturality of the canonical acyclic-resolution comparison with the identity
coefficient map. Cancel the inverse target comparison to obtain equality of the
hom maps. Compose with the terminal-source Ext precomposition and the canonical
site-sections comparison. Evaluating this equality on z gives the assertion.
This uses no morphism of schemes and includes degree zero, zero F and empty X. -/
theorem abelian_resolution_comparison_evaluation (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (I : InjectiveResolution F)
    (R : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F))
    (φ : ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex ⟶ R.cocomplex)
    (hφ : (HomologicalComplex.singleMapHomologicalComplex
      (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)) (.up ℕ) 0).inv.app F ≫
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapHomologicalComplex
        (.up ℕ)).map I.ι ≫ φ = R.ι)
    (p : ℕ) (z : H F p) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).map φ))
      ((abelianResolutionIso X I p).hom z) =
    (abelianInjectiveResolutionIso X F R p).hom z := by
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso ι := by
    dsimp only [ι]
    have : QuasiIso ((T.mapHomologicalComplex (.up ℕ)).map I.ι) := inferInstance
    exact quasiIso_comp _ _
  have hw : ι ≫ φ = (CochainComplex.single₀ _).map (𝟙 (T.obj F)) ≫ R.ι := by
    rw [(CochainComplex.single₀ _).map_id, Category.id_comp]
    simpa only [ι, Category.assoc] using hφ
  have hc := acyclicComparison_naturality (abelianSections X) ι R.ι
    (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n))
    (fun n ↦ Functor.rightAcyclic_of_injective (R.cocomplex.X n))
    (𝟙 (T.obj F)) φ hw p
  rw [((abelianSections X).rightDerived p).map_id, Category.comp_id] at hc
  have hh :
      ((abelianSections X).rightDerivedObjIsoOfResolution ι
        (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p).hom ≫
        HomologicalComplex.homologyMap
          (((abelianSections X).mapHomologicalComplex (.up ℕ)).map φ) p =
      ((abelianSections X).rightDerivedObjIsoOfResolution R.ι
        (fun n ↦ Functor.rightAcyclic_of_injective (R.cocomplex.X n)) p).hom := by
    rw [← cancel_mono
      ((abelianSections X).rightDerivedObjIsoOfResolution R.ι
        (fun n ↦ Functor.rightAcyclic_of_injective (R.cocomplex.X n)) p).inv]
    rw [Category.assoc, hc]
    simp only [Iso.hom_inv_id]
  have hsource : abelianResolutionIso X I p =
      abelianExtSectionsIso X F p ≪≫
        (abelianSections X).rightDerivedObjIsoOfResolution ι
          (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p := by
    delta abelianResolutionIso abelianExtSectionsIso
    exact (Iso.trans_assoc _ _ _).symm
  have he : (abelianResolutionIso X I p).hom ≫
      HomologicalComplex.homologyMap
        (((abelianSections X).mapHomologicalComplex (.up ℕ)).map φ) p =
      (abelianInjectiveResolutionIso X F R p).hom := by
    rw [hsource]
    delta abelianInjectiveResolutionIso
    simp only [Iso.trans_hom, Category.assoc]
    rw [hh]
  exact ConcreteCategory.congr_hom he z

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
