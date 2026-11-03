/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeightsEmbedding
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Transport of mixed filtrations along scalar equivalences

Source: def-weil-frobenius-module-weights, transport of the finite stable filtration
(blueprint: lem-a1-mixed-embedding-semilinear-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v u' v'

namespace FrobeniusModule

local instance {K : Type v} {L : Type v'} [Field K] [Field L] (σ : K ≃+* L) :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ

local instance {K : Type v} {L : Type v'} [Field K] [Field L] (σ : K ≃+* L) :
    RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.of_ringEquiv_symm σ

/-- Mixed filtrations transport through an equivariant semilinear equivalence.
Source: the finite stable-filtration definition, def-weil-frobenius-module-weights.
Proof: map the filtration along the equivalence, restrict it on each filtration term,
and pass to successive quotients. Conjugate each graded automorphism. Eigenvectors
transport semilinearly, so their eigenvalues and complex norms have the required values.
This includes the zero-length filtration and zero graded pieces.
(blueprint: lem-a1-mixed-embedding-semilinear-transport). -/
theorem IsMixedOfWeightsAtMostEmbedding.of_semilinearEquiv
    {K : Type v} {L : Type v'} [Field K] [Field L]
    (σ : K ≃+* L) (iota : L →+* ℂ) (q : ℕ)
    {M : FrobeniusModule.{u, v} K} {N : FrobeniusModule.{u', v'} L}
    (e : M.carrier ≃ₛₗ[σ.toRingHom] N.carrier)
    (he : ∀ x, e (M.frobenius x) = N.frobenius (e x)) {w : ℝ}
    (h : IsMixedOfWeightsAtMostEmbedding (iota.comp σ.toRingHom) q M w) :
    IsMixedOfWeightsAtMostEmbedding iota q N w := by
  classical
  obtain ⟨m, V, hzero, hwhole, hinc, hstable, hgraded⟩ := h
  let W := fun r ↦ (V r).map e.toLinearMap
  refine ⟨m, W, ?_, ?_, ?_, ?_, ?_⟩
  · simp [W, hzero]
  · simp [W, hwhole]
  · intro r
    exact Submodule.map_mono (hinc r)
  · intro r
    have he' : N.frobenius.toLinearMap.comp e.toLinearMap =
        e.toLinearMap.comp M.frobenius.toLinearMap := by
      ext x
      exact (he x).symm
    change ((V r).map e.toLinearMap).map N.frobenius.toLinearMap = _
    rw [← Submodule.map_comp, he', Submodule.map_comp, hstable]
  · intro r
    obtain ⟨wr, G, hwr, hG, hpure⟩ := hgraded r
    let er := e.ofSubmodules (V r.succ) (W r.succ) rfl
    let P := (V r.castSucc).comap (V r.succ).subtype
    let Q := (W r.castSucc).comap (W r.succ).subtype
    have hPQ : P.map er.toLinearMap = Q := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Submodule.mem_map_of_mem hx
      · intro hy
        obtain ⟨x, hx, hexy⟩ := hy
        refine ⟨⟨x, hinc r hx⟩, hx, ?_⟩
        exact Subtype.ext hexy
    let eq := Submodule.Quotient.equiv P Q er hPQ
    let H : (↥(W r.succ) ⧸ Q) ≃ₗ[L] (↥(W r.succ) ⧸ Q) :=
      (eq.symm.trans G).trans eq
    refine ⟨wr, H, hwr, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, rfl⟩ := er.surjective y
      have hx : M.frobenius (x : M.carrier) ∈ V r.succ := by
        exact (congrArg (fun S : Submodule K M.carrier ↦
          M.frobenius (x : M.carrier) ∈ S) (hstable r.succ)).mp
            (Submodule.mem_map_of_mem x.property)
      change eq (G (eq.symm (Submodule.Quotient.mk (er x)))) = _
      have hq : eq (Submodule.Quotient.mk x) = Submodule.Quotient.mk (er x) := rfl
      rw [← hq, eq.symm_apply_apply, hG x hx]
      change Submodule.Quotient.mk (er ⟨M.frobenius x, hx⟩) = _
      congr 1
      apply Subtype.ext
      exact he x
    · intro α hα
      obtain ⟨y, hy⟩ := hα.exists_hasEigenvector
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
      have hx : Module.End.HasEigenvalue G.toLinearMap (σ.symm α) := by
        apply Module.End.hasEigenvalue_of_hasEigenvector (x := eq.symm y)
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
        refine ⟨?_, ?_⟩
        · apply eq.injective
          change H y = eq (σ.symm α • eq.symm y)
          have hy' : H y = α • y := hy.1
          rw [map_smulₛₗ]
          change H y = σ (σ.symm α) • eq (eq.symm y)
          rw [σ.apply_symm_apply, eq.apply_symm_apply]
          exact hy'
        · intro hz
          exact hy.2 (eq.symm.injective (hz.trans (map_zero eq.symm).symm))
      simpa using hpure (σ.symm α) hx

end FrobeniusModule
