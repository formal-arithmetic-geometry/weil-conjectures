/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients

/-!
# Right exactness of the Kummer coefficient twist

Source: blueprint sk-prop-a1-kummer, Coefficients; Stacks Project, Tag 03EK.
(blueprint: lem-pur-kummer-twist-right-exact).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- The actual Kummer coefficient twist preserves finite colimits.
Source: blueprint sk-prop-a1-kummer, Coefficients; Stacks Project, Tag 03EK.
(blueprint: lem-pur-kummer-twist-right-exact).

Proof: evaluate the sectionwise tensor functor at each site object. It is the composite
of evaluation with tensoring by the fixed root module there. Module categories are
monoidal closed, so this tensor functor preserves colimits. Evaluation detects colimits
in the presheaf category. Thus the whole presheaf tensor functor preserves colimits.
Compose it with the constant-presheaf functor and the sheafification left adjoint;
both preserve colimits. In particular the resulting Kummer twist preserves finite colimits.
This uses no flatness or freeness hypothesis on the coefficient module. -/
theorem kummerModuleTwist_preservesFiniteColimits (X : Scheme.{u}) (m : ℕ) :
    PreservesFiniteColimits (kummerModuleTwist X m) := by
  have : PreservesColimits (tensorLeft (kummerRootModulePresheaf X m)) := by
    apply preservesColimits_of_evaluation
    intro U
    change PreservesColimits ((CategoryTheory.evaluation X.Etaleᵒᵖ _).obj U ⋙
      tensorLeft ((kummerRootModulePresheaf X m).obj U))
    infer_instance
  unfold kummerModuleTwist
  infer_instance

end AlgebraicGeometry.Scheme
