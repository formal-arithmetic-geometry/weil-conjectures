/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeightsEmbedding

/-! Eigenvalue bounds read from a finite mixed filtration.
Source: latest blueprint, def-weil-frobenius-module-weights and the curve-upper step of
lem-zl-relative-curve-punctual.proof.md.
-/

@[expose] public section
set_option autoImplicit false
universe u v
namespace FrobeniusModule

/-- A finite mixed filtration bounds every eigenvalue for an arbitrary field embedding.
Source: latest blueprint, finite-filtration definition, and relative-curve proof step 4
(blueprint: lem-zl-mixed-embedding-eigenvalue-bound).
Proof: follow a nonzero eigenvector up the filtration. In the first piece containing it,
its image in the preceding quotient is nonzero and is an eigenvector with the same
eigenvalue. The pure quotient has weight at most w. Monotonicity of q to real powers
for q >= 1 gives the bound. The zero-length filtration has no nonzero eigenvectors. -/
theorem IsMixedOfWeightsAtMostEmbedding.eigenvalue_bound
    {K : Type v} [Field K] (iota : K →+* ℂ) (q : ℕ) (hq : (1 : ℝ) ≤ q)
    (M : FrobeniusModule.{u, v} K) (w : ℝ)
    (hM : IsMixedOfWeightsAtMostEmbedding iota q M w) :
    M.HasWeightsAtMost iota q w := by
  classical
  obtain ⟨m, V, hzero, hwhole, _, hstable, hpure⟩ := hM
  intro α hα
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  have hfil : ∀ r : Fin (m + 1), ∀ y : M.carrier,
      y ∈ V r → M.frobenius y = α • y → y ≠ 0 →
      ‖iota α‖ ≤ (q : ℝ) ^ (w / 2) := by
    intro r
    induction r using Fin.induction with
    | zero =>
        intro y hy _ hne
        exact (hne (by simpa [hzero] using hy)).elim
    | succ r ih =>
        intro y hy hFy hne
        by_cases hprev : y ∈ V r.castSucc
        · exact ih y hprev hFy hne
        · obtain ⟨wr, G, hwr, hG, hp⟩ := hpure r
          let z : V r.succ := ⟨y, hy⟩
          have hz : (Submodule.Quotient.mk z :
              ↥(V r.succ) ⧸ (V r.castSucc).comap (V r.succ).subtype) ≠ 0 := by
            simpa [Submodule.Quotient.mk_eq_zero, z] using hprev
          have hFy' : M.frobenius y ∈ V r.succ := by
            rw [← hstable r.succ]
            exact Submodule.mem_map_of_mem hy
          have heig : (FrobeniusModule.frobeniusEnd
              { carrier := ↥(V r.succ) ⧸ (V r.castSucc).comap (V r.succ).subtype
                frobenius := G }).HasEigenvalue α := by
            apply Module.End.hasEigenvalue_of_hasEigenvector (x := Submodule.Quotient.mk z)
            rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
            refine ⟨?_, hz⟩
            change G (Submodule.Quotient.mk z) = α • Submodule.Quotient.mk z
            rw [hG z hFy']
            change Submodule.Quotient.mk (⟨M.frobenius y, hFy'⟩ : V r.succ) =
              Submodule.Quotient.mk (α • z)
            congr 1
            exact Subtype.ext hFy
          have hnorm : ‖iota α‖ = (q : ℝ) ^ (wr / 2) := hp α heig
          exact hnorm.le.trans (Real.rpow_le_rpow_of_exponent_le hq
            (div_le_div_of_nonneg_right hwr (by norm_num)))
  exact hfil (Fin.last m) x (by rw [hwhole]; exact Submodule.mem_top) hx.1 hx.2

end FrobeniusModule
