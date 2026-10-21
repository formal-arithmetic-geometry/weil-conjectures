/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite projective module evaluation and coevaluation

Source: literature/stacks-project/modules.tex, Tags 0FNV and 0FNJ
(blueprint: lem-zl-finite-projective-module-dual-pairing).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open TensorProduct

namespace LinearMap

/-- The canonical tensor-to-endomorphism equivalence for a finite projective module.

Source: Stacks Project, modules.tex, Tag 0FNV, Example `modules-example-dual`
(blueprint: lem-zl-finite-projective-module-dual-pairing). -/
noncomputable def finiteProjectiveTensorEndEquiv (A : Type u) [CommRing A]
    (P : Type v) [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Projective A P] : P ⊗[A] Module.Dual A P ≃ₗ[A] P →ₗ[A] P :=
  (TensorProduct.comm A P (Module.Dual A P)).trans
    (dualTensorHomEquiv A P P)

/-- The canonical evaluation map `P^vee ⊗ P → A`.

Source: Stacks Project, modules.tex, Tag 0FNV, Example `modules-example-dual`
(blueprint: lem-zl-finite-projective-module-dual-pairing). -/
def finiteProjectiveEvaluation (A : Type u) [CommRing A]
    (P : Type v) [AddCommGroup P] [Module A P] :
    Module.Dual A P ⊗[A] P →ₗ[A] A :=
  contractLeft A P

/-- The coevaluation map obtained by sending `1` to the tensor corresponding to the identity.

Source: Stacks Project, modules.tex, Tag 0FNV, Example `modules-example-dual`
(blueprint: lem-zl-finite-projective-module-dual-pairing). -/
noncomputable def finiteProjectiveCoevaluation (A : Type u) [CommRing A]
    (P : Type v) [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Projective A P] : A →ₗ[A] P ⊗[A] Module.Dual A P :=
  LinearMap.toSpanSingleton A _
    ((finiteProjectiveTensorEndEquiv A P).symm (LinearMap.id : P →ₗ[A] P))

/-- The canonical tensor-to-endomorphism map underlying the equivalence above.

Source: Stacks Project, modules.tex, Tag 0FNV, Example `modules-example-dual`
(blueprint: lem-zl-finite-projective-module-dual-pairing). -/
noncomputable def finiteProjectiveTensorEndMap (A : Type u) [CommRing A]
    (P : Type v) [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Projective A P] : P ⊗[A] Module.Dual A P →ₗ[A] P →ₗ[A] P :=
  (finiteProjectiveTensorEndEquiv A P).toLinearMap

/--
For a commutative ring `A` and a finitely generated projective `A`-module `P`, the ordinary
 dual is finitely generated projective.  Evaluation is contraction, and the tensor-to-endomorphism
 equivalence identifies the tensor corresponding to the identity with coevaluation.  The two
 displayed composites are the left and right triangle identities, with the canonical tensor
 associators and unitors.

Source: Stacks Project, modules.tex, Tag 0FNV, Example `modules-example-dual`, and Tag 0FNJ,
More on Algebra, Lemma `lemma-left-dual` (blueprint: lem-zl-finite-projective-module-dual-pairing).

Proof steps: (1) `lem-sf-finite-projective-dual` gives finite generation and projectivity of the
ordinary dual. (2) `lem-pc-finite-projective-module-tensor-hom`, specialized to `M = P`,
`Q = A`, identifies the canonical tensor-to-Hom map; the right unitor identifies its target with
`End_A(P)`, and `contractLeft` is evaluation. (3) Taking the inverse image of `id_P` gives the
coevaluation tensor; expanding it as a finite dual-basis sum proves both triangle composites,
including the zero and rank-one cases.
-/
theorem finiteProjectiveModuleDualPairing (A : Type u) [CommRing A]
    (P : Type v) [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Projective A P] :
    Module.Finite A (Module.Dual A P) ∧ Module.Projective A (Module.Dual A P) ∧
      Function.Bijective (finiteProjectiveTensorEndMap A P) ∧
      (TensorProduct.rid A P).toLinearMap ∘ₗ
          (LinearMap.lTensor P (finiteProjectiveEvaluation A P)) ∘ₗ
            (TensorProduct.assoc A P (Module.Dual A P) P).toLinearMap ∘ₗ
              (finiteProjectiveCoevaluation A P).rTensor P ∘ₗ
                (TensorProduct.lid A P).symm.toLinearMap = (LinearMap.id : P →ₗ[A] P) ∧
      (TensorProduct.lid A (Module.Dual A P)).toLinearMap ∘ₗ
          (finiteProjectiveEvaluation A P).rTensor (Module.Dual A P) ∘ₗ
            (TensorProduct.assoc A (Module.Dual A P) P (Module.Dual A P)).symm.toLinearMap ∘ₗ
              (finiteProjectiveCoevaluation A P).lTensor (Module.Dual A P) ∘ₗ
                (TensorProduct.rid A (Module.Dual A P)).symm.toLinearMap =
        (LinearMap.id : Module.Dual A P →ₗ[A] Module.Dual A P) := by
  have left (t : P ⊗[A] Module.Dual A P) (y : P) :
      TensorProduct.rid A P
          ((finiteProjectiveEvaluation A P).lTensor P
            (TensorProduct.assoc A P (Module.Dual A P) P (t ⊗ₜ[A] y))) =
        finiteProjectiveTensorEndEquiv A P t y := by
    induction t using TensorProduct.induction_on with
    | zero => simp [finiteProjectiveTensorEndEquiv]
    | tmul x f =>
      simp [finiteProjectiveEvaluation, finiteProjectiveTensorEndEquiv,
        dualTensorHomEquiv]
    | add t₁ t₂ h₁ h₂ => simp [add_tmul, h₁, h₂]
  have right (t : P ⊗[A] Module.Dual A P) (f : Module.Dual A P) (y : P) :
      TensorProduct.lid A (Module.Dual A P)
          ((finiteProjectiveEvaluation A P).rTensor (Module.Dual A P)
            ((TensorProduct.assoc A (Module.Dual A P) P (Module.Dual A P)).symm
              (f ⊗ₜ[A] t))) y =
        f (finiteProjectiveTensorEndEquiv A P t y) := by
    induction t using TensorProduct.induction_on with
    | zero => simp [finiteProjectiveTensorEndEquiv]
    | tmul x g =>
      simp [finiteProjectiveEvaluation, finiteProjectiveTensorEndEquiv,
        dualTensorHomEquiv, mul_comm]
    | add t₁ t₂ h₁ h₂ => simp [tmul_add, h₁, h₂]
  let c := (finiteProjectiveTensorEndEquiv A P).symm (LinearMap.id : P →ₗ[A] P)
  have hc : finiteProjectiveTensorEndEquiv A P c = LinearMap.id :=
    (finiteProjectiveTensorEndEquiv A P).apply_symm_apply _
  refine ⟨inferInstance, inferInstance,
    (finiteProjectiveTensorEndEquiv A P).bijective, ?_, ?_⟩
  · ext y
    simpa [finiteProjectiveCoevaluation, c] using
      (left c y).trans (congrArg (fun g : P →ₗ[A] P ↦ g y) hc)
  · ext f y
    simpa [finiteProjectiveCoevaluation, c] using
      (right c f y).trans (congrArg (fun g : P →ₗ[A] P ↦ f (g y)) hc)

end LinearMap
