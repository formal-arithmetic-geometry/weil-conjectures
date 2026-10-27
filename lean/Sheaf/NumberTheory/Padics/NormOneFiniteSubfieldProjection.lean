/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.Padics.ProperSpace
import Sheaf.Analysis.Normed.Module.AdmissibleScalarBalls
import Sheaf.Analysis.Normed.Module.ContractiveExtensionFromAdmissibleValues

/-! # Norm-one projection onto a finite p-adic subfield

Source: Weil blueprint, main-20261015, `sec-six-functors-basics`,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), scalar tame-kernel expansion
(blueprint: lem-sfb-norm-one-finite-subfield-projection).

The algebraic closure has the extending nonarchimedean norm. Intermediate fields inherit
that norm and its topology. No completeness of the algebraic closure is required.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Padic

/-- A finite intermediate p-adic field admits a contractive linear retraction from the
normed algebraic closure. Bundling continuity records the stated consequence of the bound.

Source: Weil blueprint, main-20261015, `sec-six-functors-basics`,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), scalar tame-kernel expansion
(blueprint: lem-sfb-norm-one-finite-subfield-projection).

Proof:
1. The norm of F is the restriction of the norm of Ω by construction. By
   FiniteDimensional.proper, its closed balls are compact. The ultrametric inequality
   on Ω restricts to F. Identify F with the range W of its F-linear inclusion into Ω;
   the inverse f : W →ₗ[F] F is isometric.
2. Apply lem-sfb-admissible-scalar-balls with K = F and V = Ω. Compactness from step 1
   supplies its closed-ball hypothesis, so every contractive partial functional admits
   a scalar satisfying all constraints for a one-vector extension.
3. Apply lem-sfb-contractive-extension-from-admissible-values to the nonnegative norms,
   W, and f. The normed-field axioms give multiplicativity and scalar homogeneity;
   step 1 gives the ultrametric inequalities and the bound on f. The resulting linear
   h : Ω →ₗ[F] F extends f and satisfies ‖h x‖ ≤ ‖x‖. Evaluating its extension property
   at the image of a : F gives h a = a.
4. LinearMap.mkContinuous with bound 1 bundles h as a continuous linear map without
   changing its values. It still fixes F and satisfies the same bound. Neither input
   requires completeness of Ω; all compactness occurs in F.
-/
theorem exists_normOne_finiteSubfield_projection
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] [IsUltrametricDist Ω]
    (F : IntermediateField (Padic l) Ω) [FiniteDimensional (Padic l) F] :
    ∃ p : Ω →L[F] F, (∀ a : F, p (a : Ω) = a) ∧ ∀ x : Ω, ‖p x‖ ≤ ‖x‖ := by
  classical
  let : NormedSpace F Ω :=
    { norm_smul_le := fun a x ↦ (norm_mul (a : Ω) x).le }
  have : ProperSpace F := FiniteDimensional.proper (Padic l) F
  have hF : ∀ a b : F, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := fun a b ↦
    IsUltrametricDist.norm_add_le_max (a : Ω) (b : Ω)
  have hΩ : ∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
    IsUltrametricDist.norm_add_le_max
  let i : F →ₗ[F] Ω := Algebra.linearMap F Ω
  let e : F ≃ₗ[F] LinearMap.range i :=
    LinearEquiv.ofInjective i (algebraMap F Ω).injective
  have he (w : LinearMap.range i) : (e.symm w : Ω) = (w : Ω) :=
    congrArg Subtype.val (e.apply_symm_apply w)
  have hf (w : LinearMap.range i) : ‖e.symm w‖₊ ≤ ‖(w : Ω)‖₊ := by
    change ‖(e.symm w : Ω)‖ ≤ ‖(w : Ω)‖
    rw [he]
  obtain ⟨h, hfix, hbound⟩ := LinearMap.exists_contractive_extension_of_admissible_values
    (nnnorm : F → NNReal) (nnnorm : Ω → NNReal)
    (fun a ↦ nnnorm_eq_zero) (nnnorm_one)
    (fun a b ↦ nnnorm_mul a b) (fun a b ↦ hF a b)
    (fun x ↦ nnnorm_eq_zero) (fun a x ↦ nnnorm_smul a x) (fun x y ↦ hΩ x y)
    (fun U g hg x hx ↦
      LinearMap.exists_admissible_scalar_of_isCompact_closedBall hF hΩ
        (fun a r _ ↦ isCompact_closedBall a r) U g hg x hx)
    (LinearMap.range i) e.symm.toLinearMap hf
  have hbound' (x : Ω) : ‖h x‖ ≤ ‖x‖ := hbound x
  refine ⟨h.mkContinuous 1 (fun x ↦ by simpa only [one_mul] using hbound' x), ?_, ?_⟩
  · intro a
    change h (e a : Ω) = a
    exact (hfix (e a)).trans (e.symm_apply_apply a)
  · exact hbound'

end Padic
