/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # Degree-zero restricted resolution section classes

Source: Stacks Project, Cohomology, Tag 01E4.
(blueprint: lem-weil-pbc-resolution-section-class-zero-augmentation).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- The class of an augmented restricted section is the direct-image augmentation
of the same section on the original open.
Source: Stacks Project, Cohomology, Tag 01E4 (lemma-describe-higher-direct-images).
(blueprint: lem-weil-pbc-resolution-section-class-zero-augmentation).

Proof: Expand the two canonical augmentations using
InjectiveResolution.toRightDerivedZero_eq. Cancel the inverse derived-resolution
comparison on the right. The augmentation equation of R and its pinned degree-zero
section component identify the section zero-cycle with the augmentation of s in I.
Naturality of the cycles-to-homology projection transports this identity to homology.
The sheafification adjunction defining sectionCohomologyTheta sends that class to
its homology-sheaf class: the counit is the identity on the original sheaf complex,
and exact sheafification commutes with its cycles and homology. Thus the section
class followed by the inverse resolution comparison is precisely the canonical
augmentation evaluated on the section identified by restrictAppIso. This argument
uses no special hypothesis on f or F and includes the empty open and zero section. -/
theorem resolutionSectionClass_zero_augmentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (I : InjectiveResolution F) (V : Y.Opens)
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V))
    (s : ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F).presheaf.obj (op ⊤)) :
    (resolutionSectionClass R.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V R.sections 0 ≫ Hom.app (I.isoRightDerivedObj (pushforward f) 0).inv V)
        (((RingedSpace.globalSectionsFunctor
          (f ⁻¹ᵁ V).toScheme.toRingedSpace).toRightDerivedZero.app
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).hom s) =
    (Hom.app
      ((pushforward f).toRightDerivedZero.app F) V)
        (F.presheaf.map (eqToHom (f ⁻¹ᵁ V).ι_image_top.symm).op
          ((F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).hom s)) := by sorry

end AlgebraicGeometry.Scheme.Modules
