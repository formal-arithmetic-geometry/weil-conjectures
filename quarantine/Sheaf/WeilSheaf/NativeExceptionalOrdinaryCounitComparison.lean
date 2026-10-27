/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetfulData

/-! # Ordinary exceptional counit comparison

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, first comparison step.
(blueprint: lem-sf-native-exceptional-ordinary-counit-comparison).

This is the comparison-isomorphism part of the ordinary exceptional counit
construction. The remaining witness and graded Hom assertions are separated
into a second statement so that the main theorem only assembles independent
parts of the construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- The normalized ordinary exceptional comparison exists.

Proof source: cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence. Choose the native compactification, compose
the unit-normalized open/proper forgetting comparison with the inverse of the
scalar-normalized compact-support realization, and transport it through the
closure and section-module comparisons. Full faithfulness of the specified
realization lifts the resulting ordinary comparison to the supplied
ForgetModels; compactification refinement identifies it with the given
coefficient system and compactification.
(blueprint: lem-sf-native-exceptional-ordinary-counit-comparison). -/
theorem native_exceptional_ordinary_counit_comparison (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀)) :
    Nonempty (nativeShriek D l f₀ ⋙ VY.functor ≅
        VX.functor ⋙ (S.ring.operation c .closed).F) := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
