/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.FormalFibreCohomology
import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation
import Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # Canonical theta on augmented sections

Source: Stacks Project, Cohomology, Tags 01E4 and 01FB, degree-zero formulas.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-augmented-sections).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A canonical theta sends the fixed direct-image augmentation of a germ of a section
of any module to the global-sections augmentation of its tensor-pullback unit image.
Source: Stacks Project, Cohomology, Tags 01E4 and 01FB (degree zero).
(blueprint: lem-weil-pbc-formal-functions-degree-zero-augmented-sections).

Proof: Choose an injective resolution I of F and a resolution J of its tensor
pullback F'. Restrict these termwise to U = f inverse V and W = i_n inverse U.
Restriction is exact and preserves injectives, so these give the restricted
resolutions in FlatBaseChangeOpenChoices. Define psi by restricting the tensor
adjunction unit and transposing under the restriction adjunction; functoriality
of pushforward gives its unit square. No flatness of i_n is used. Identify
sections by restrictAppIso and the inclusion-image-top equality.
Augment the restriction of t to U by the global-sections toRightDerivedZero map,
obtaining xi. Express this map using InjectiveResolution.toRightDerivedZero_eq.
The augmentation and component equations of the restricted resolution identify
the resulting zero-cycle with I's augmentation of t on U. The section class
map takes this cycle to its homology-sheaf class by the sheafification counit;
its composite with the inverse resolution comparison is thus the direct-image
augmentation of t on V. Naturality of germs identifies its germ with the stalk
augmentation applied to germ(t). Apply IsFormalFunctionsTheta to xi.
The zero-augmentation square for the cohomology h-map of psi identifies the
right side with the augmented restriction of the original tensor-unit image
of t, by the unit square. The inequality hV identifies W with top. On this
open the restriction of sections is an isomorphism, as are the degree-zero
augmentation maps, so the degree-zero cohomology restriction is injective.
Cancel it to get the claimed equality. Empty fibres, the zero module and t=0
are covered by the same augmentation identities. -/
theorem formalFunctions_degreeZero_augmented_sections {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) (F : X.Modules) (n : ℕ)
    (θ : formalFunctionsStalk f y F 0 →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F 0 n)
    (hθ : IsFormalFunctionsTheta f y F 0 n θ)
    (V : Y.Opens) (hy : y ∈ V)
    (hV : (⊤ : (formalFibre f y n).Opens) ≤
      (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
    (t : F.presheaf.obj (op (f ⁻¹ᵁ V))) :
    θ (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app F)).hom
        (TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj F).val.presheaf
          V y hy t)) =
    ((RingedSpace.globalSectionsFunctor (formalFibre f y n).toRingedSpace).toRightDerivedZero.app
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)).hom
      (((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F).presheaf.map
        (homOfLE hV).op
          ((((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
            (formalFibreι f y n))).unit.app F).val.app (op (f ⁻¹ᵁ V))).hom t)) := by sorry

end AlgebraicGeometry
