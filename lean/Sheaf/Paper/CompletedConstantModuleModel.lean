/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.CompletedConstantRealizationData

/-! # Tensor realization of finite completion modules

Source: Stacks Tags 0912, 093J--093M and 09BT.
(blueprint: lem-weil-pbc-completed-constant-module-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Scalar extension realizes the compatible finite quotient module model.
Source: Stacks Tag 0912 (lemma-limit-flat), Tags 093J--093M and Tag 09BT, clause (3).
(blueprint: lem-weil-pbc-completed-constant-module-model).

Proof: put C = AdicCompletion I A and J = I C. Completion is Noetherian and J-complete,
and evaluation identifies C/J^(n+1) with A/I^(n+1). A finite C-module N is complete and
finitely presented. Its reduction modulo J is finite as a module over C/J = A/I.
On a site object U, the constant sections of C/J^(n+1) are flat over that quotient;
their transition maps are surjective. The limit-flat tensor theorem identifies
N tensor_C H(U) with the limit of the constant quotient-module sections. The
finitely presented constant-section tensor comparison identifies this with the
sections of H tensor_(constant C) constant N. These comparisons are natural in U
and N, and send a tensor to its projected scalar times the residue of N.
Consequently they sheafify to the specified realization isomorphisms; the same
formula gives their linearity and naturality. H is flat over constant C by 093M
applied to (C,J), so the exact constant functor followed by scalar extension is
exact. Restricting to finite modules preserves their finite limits and colimits.
Finally N, restricted to A, is I-complete; its quotient by I is finite over A/I.
Use the maximal covering sieve and the realization isomorphism on every object
for the adic-lisse local model. The projected tensor formula gives its scalar law.
The argument includes the zero ring, I = 0, I = top, and N = 0. -/
theorem completed_constant_module_model (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) :
    ∃ d : CompletedConstantModuleRealization X I, d.scalar = φ := by
  sorry

end AlgebraicGeometry.Scheme
