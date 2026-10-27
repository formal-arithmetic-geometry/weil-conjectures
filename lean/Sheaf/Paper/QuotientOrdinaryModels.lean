/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientReductionCore

/-! # Normalization of ordinary quotient reduction

Source: Zheng Construction 4.1; Stacks 03EK and 06YY.
(blueprint: lem-pur-quotient-ordinary-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
variable (R : Sheaf J CommRingCat.{max c v r})
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (α : ∀ n : ℕ, R ⟶ B n)
  (hα : ∀ n : ℕ, α (n + 1) ≫ τ n = α n)

/-- Evaluation of ordinary scalar extension, normalized on the scalar unit.
Source: Zheng Construction 4.1; Stacks 03EK, 03D7, 06YY and 07A6
(blueprint: lem-pur-quotient-ordinary-models).
Proof: the given scalar models have the prescribed sheafified extension functors.
Evaluation of the
sheafified sectionwise extension is extension at the selected vertical slice:
vertical sheafification commutes with slice restriction. The sectionwise
identity on b tensor x gives a natural isomorphism between these two functors;
it and its inverse respect balancing, restrictions, addition and scalar action,
and descend through sheafification. On 1 tensor x this is the displayed unit
normalization. No complex,
flatness, tensor totalization, or invertibility in a derived category is used. -/
theorem quotientOrdinaryModels
    (scalar : ScalarData.{c, v, max c v r}
      (quotientRingMap.{c, v, r} J R B τ α hα))
    (levels : ∀ n : ℕ, ScalarData.{c, v, max c v r} (α n)) :
    ∃ reductionEvaluation : ∀ n : ℕ,
      quotientConstant.{c, v, r} J R ⋙ scalar.model.E ⋙
        evaluation.{c, v, max c v r} J B τ n ≅ (levels n).model.E,
(∀ (M : Mod.{c, v, max c v r} J R) (n : ℕ) (U : Cᵒᵖ)
    (x : M.val.obj U)
    (y : ((evaluation.{c, v, max c v r} J B τ n).obj
      (scalar.model.E.obj ((quotientConstant.{c, v, r} J R).obj M))).val.obj U),
    HEq y (scalarExtensionSection.{c, v, r} (quotientRingMap.{c, v, r} J R B τ α hα)
      scalar ((quotientConstant.{c, v, r} J R).obj M) (op (n, U.unop)) x) →
    HEq (((reductionEvaluation n).hom.app M).val.app U y)
      (scalarExtensionSection.{c, v, r} (α n) (levels n) M U x)) := by sorry

end WeilConjectures.SemilinearSections
