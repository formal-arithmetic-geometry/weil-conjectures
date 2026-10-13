/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.HigherDirectImagePresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.Topology.RestrictInjectiveResolution
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact

/-! # Coefficient-natural comparison with resolution section cohomology

Source: Stacks Project, Cohomology, Tags 01E1 and 01E4.
(blueprint: lem-pc-higher-direct-image-coefficient-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Scheme.Modules.enoughInjectives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The comparison from cohomology on inverse-image opens to higher-image sections
is natural in coefficients. Its component is the resolution comparison followed by
canonical theta. This asserts no detection of morphisms on an affine basis.

Source: Stacks Project, Cohomology, Lemmas 20.7.1 and 20.7.3, Tags 01E1 and 01E4.
(blueprint: lem-pc-higher-direct-image-coefficient-comparison).

Proof: Restrict an injective resolution I to U = f inverse image V using exact open
restriction and its exact left adjoint. Transport through overEquiv to the module
category of U.toScheme. The augmentation is the restricted augmentation, and
restrictAppIso at the terminal open identifies global sections of every term with
sections of I on U. Forgetting the global scalar action is exact, so mapHomologyIso
identifies module cohomology with homology of this section complex. Evaluation of
f_*I on V is the same section complex. These isomorphisms give e. Compose e with
theta and the inverse of isoRightDerivedObj to obtain the component c. To prove
coefficient naturality, lift a coefficient map to injective resolutions and restrict
that lift. The augmentations still commute. Naturality of isoRightDerivedObj and
mapHomologyIso, and of the sheafification unit and counit defining theta, gives the
naturality square. Any two such lifts are homotopic, so induce the same homology
map. Comparing chosen resolutions with arbitrary I proves the displayed formula
for every I. This applies in degree zero and to the empty inverse-image open:
restriction and the section comparisons have the same definitions in these cases. -/
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
        (show SheafOfModules (moduleRings X.toRingedSpace) from N)) (V : Y.Opens),
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
                      (Opposite.op V) := by sorry

end AlgebraicGeometry
