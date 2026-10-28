/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetfulData

/-! # Canonical-model ordinary exceptional comparison

This isolates the comparison for the canonical family of forgetful models. The
main comparison theorem transports this result to arbitrary supplied models.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, first comparison step.
(blueprint: lem-sf-native-exceptional-ordinary-counit-model-comparison).
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

/-- The canonical forgetful-model comparison exists for every coefficient system.

Proof source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-
adjunction sentence. The native compactification and normalized open/proper and
scalar comparisons construct a canonical family of ForgetModels and its left
ordinary comparison. This is strictly the canonical-model part; transport to
arbitrary supplied ForgetModels is proved by the parent theorem.
(blueprint: lem-sf-native-exceptional-ordinary-counit-model-comparison). -/
theorem native_exceptional_ordinary_counit_model_comparison (R : Family l D) :
    ∃ model : ∀ T : Space D, ForgetModel D l R T,
      ∀ (X Y : Space D) (f₀ : X.base ⟶ Y.base)
        [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
        (S : CoefficientSystem D l f₀)
        (c : Compactification (geometricMap D f₀)),
      Nonempty (nativeShriek D l f₀ ⋙ (model Y).functor ≅
        (model X).functor ⋙ (S.ring.operation c .closed).F) := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
