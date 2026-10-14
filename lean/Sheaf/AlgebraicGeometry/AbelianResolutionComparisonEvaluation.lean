/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
import Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
import Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic

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
    (abelianInjectiveResolutionIso X F R p).hom z := by sorry

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
