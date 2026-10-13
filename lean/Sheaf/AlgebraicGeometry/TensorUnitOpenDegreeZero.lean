/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.FormalFibreCohomology

/-! # Restricted tensor units in degree zero

Source: Stacks Project, Cohomology, Remark Tag 01FB, equation-choice.
(blueprint: lem-weil-pbc-tensor-unit-open-degree-zero).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- The restricted tensor-unit square commutes on augmented sections when the
inverse-image open is the whole fibre product.
Source: Stacks Project, Cohomology, Remark Tag 01FB (remark-explain-arrow),
equation-choice, specialized to degree zero.
(blueprint: lem-weil-pbc-tensor-unit-open-degree-zero).

Proof: Apply the canonical degree-zero augmentation square for moduleCohomologyFMap
first to the restricted h-map D.psi and then to the restriction-adjunction unit on
the fibre product. Their inputs are the section t identified with a section of the
restricted module by restrictAppIso, and the restriction of its tensor-unit image
along hV. The two resulting sections of the restricted tensor pullback agree:
evaluate D.unit_square at U = f inverse V and at t. PushforwardComp and
pushforwardCongr identify these with the same section on W = h inverse U;
the restriction-adjunction unit acts by restriction, and restrictAppIso identifies
sections over top with sections over U (respectively W). Since hV says W is top,
restriction from top to W followed by restriction back to top is the identity.
Naturality of restriction with the tensor unit therefore gives precisely the two
sections in question. Apply their common augmentation to obtain the equality.
No flatness is used. The calculation also applies to empty fibre products, empty
opens and zero sections. -/
theorem tensorUnit_open_degree_zero {X S : Scheme.{u}} (f : X ⟶ S) (y : S) (n : ℕ)
    (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (formalFibreι f y n)).obj F))
    (V : S.Opens) (D : FlatBaseChangeOpenChoices f (formalFibreBaseMap S y n) F I J V)
    (hV : (⊤ : (formalFibre f y n).Opens) ≤ (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
    (t : F.presheaf.obj (op (f ⁻¹ᵁ V))) :
    moduleCohomologyFMap ((formalFibreι f y n).resLE (f ⁻¹ᵁ V)
      ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi 0
        (((RingedSpace.globalSectionsFunctor
          (f ⁻¹ᵁ V).toScheme.toRingedSpace).toRightDerivedZero.app
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).hom
            ((F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).inv
              (F.presheaf.map (eqToHom (f ⁻¹ᵁ V).ι_image_top).op t))) =
    moduleCohomologyFMap ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
      ((restrictAdjunction ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
        ((tensorPullback (formalFibreι f y n)).obj F)) 0
          (((RingedSpace.globalSectionsFunctor
            (formalFibre f y n).toRingedSpace).toRightDerivedZero.app
              ((tensorPullback (formalFibreι f y n)).obj F)).hom
              (((tensorPullback (formalFibreι f y n)).obj F).presheaf.map
                (homOfLE hV).op
                  ((((Classical.choose (exists_tensorPullbackAdjunction
                    (formalFibreι f y n))).unit.app F).val.app (op (f ⁻¹ᵁ V))).hom t))) := by sorry

end AlgebraicGeometry.Scheme.Modules
