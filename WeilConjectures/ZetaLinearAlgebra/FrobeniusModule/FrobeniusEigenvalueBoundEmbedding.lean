/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeightsEmbedding
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic

/-! # Eigenvalue bounds and mixed filtrations for an arbitrary embedding

Source: sk-c-dl-a1-hc1, proof step 4, the invariant full flag argument.
(blueprint: lem-dl-a1-eigenvalue-bound-embedding)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v

namespace FrobeniusModule

/-- An upper bound for all eigenvalues gives a stable filtration with pure graded pieces.
Source: sk-c-dl-a1-hc1, proof step 4
(blueprint: lem-dl-a1-eigenvalue-bound-embedding).
Proof: choose a complete invariant flag. Finite dimensionality and injectivity make
its subspaces stable under the inverse automorphism as well. Each successive quotient
has dimension one and its scalar eigenvalue is an eigenvalue on the full space by the
subquotient spectrum lemma. Its norm is positive since Frobenius is invertible. Assign
it weight twice the logarithm of this norm divided by log q. The bound gives a weight
at most w, and all eigenvalues of that one-dimensional quotient are the same scalar.
The zero space gives the empty flag. -/
theorem isMixedOfWeightsAtMostEmbedding_of_eigenvalues
    {K : Type v} [Field K] [IsAlgClosed K]
    (iota : K →+* ℂ) (q : ℕ) (hq : 1 < q)
    (M : FrobeniusModule.{u, v} K) (w : ℝ)
    (h : ∀ α : K, M.frobeniusEnd.HasEigenvalue α → ‖iota α‖ ≤ (q : ℝ) ^ (w / 2)) :
    IsMixedOfWeightsAtMostEmbedding iota q M w := by
  classical
  obtain ⟨F, hmono, hinv, hdim⟩ :=
    Module.End.exists_complete_invariant_flag M.frobeniusEnd
  have hstable (i) : (F i).map M.frobenius.toLinearMap = F i := by
    apply Submodule.eq_of_le_of_finrank_le (hinv i)
    exact (M.frobenius.finrank_map_eq (F i)).symm.le
  have hF (i) : F i ≤ (F i).comap M.frobeniusEnd :=
    Submodule.map_le_iff_le_comap.mp (hinv i)
  refine ⟨Module.finrank K M.carrier, F, ?_, ?_, ?_, hstable, ?_⟩
  · exact Submodule.finrank_eq_zero.mp (hdim 0)
  · apply Submodule.eq_top_of_finrank_eq
    exact hdim (Fin.last _)
  · intro i
    exact hmono (Fin.castSucc_le_succ i)
  · intro i
    let L := F i.castSucc
    let U := F i.succ
    let P := L.comap U.subtype
    have hLU : L ≤ U := hmono (Fin.castSucc_le_succ i)
    let eU := M.frobenius.ofSubmodules U U (hstable i.succ)
    have hP : P.map eU.toLinearMap = P := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hF i.castSucc hy
      · intro hx
        have hx' : (x : M.carrier) ∈ F i.castSucc := hx
        rw [← hstable i.castSucc] at hx'
        obtain ⟨y, hy, hey⟩ := hx'
        refine ⟨⟨y, hLU hy⟩, hy, ?_⟩
        exact Subtype.ext hey
    let G := Submodule.Quotient.equiv P P eU hP
    have hG (x : U) : G (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (eU x) := rfl
    have hQdim : Module.finrank K (U ⧸ P) = 1 := by
      have hd := P.finrank_quotient_add_finrank
      have hp : Module.finrank K P = Module.finrank K L :=
        (Submodule.comapSubtypeEquivOfLe hLU).finrank_eq
      have hUdim : Module.finrank K U = i.val + 1 := hdim i.succ
      have hLdim : Module.finrank K L = i.val := hdim i.castSucc
      change Module.finrank K (U ⧸ P) + Module.finrank K P = Module.finrank K U at hd
      omega
    have : Nontrivial (U ⧸ P) := (Module.finrank_pos_iff (R := K)).mp (by omega)
    obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue G.toLinearMap
    obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
    have hscalar (y : U ⧸ P) : G y = α • y := by
      obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hQdim hx.2 y
      have hxe : G x = α • x := hx.apply_eq_smul
      rw [map_smul, hxe, smul_smul, smul_smul, mul_comm]
    have hαM : M.frobeniusEnd.HasEigenvalue α := by
      apply Module.End.hasEigenvalue_of_subquotient M.frobeniusEnd
        (lt_of_le_of_ne hLU ?_) (hF i.castSucc) (hF i.succ) α
      · intro y hy
        have he := hscalar (Submodule.Quotient.mk (⟨y, hy⟩ : U))
        change Submodule.Quotient.mk (eU ⟨y, hy⟩) =
          α • Submodule.Quotient.mk (⟨y, hy⟩ : U) at he
        rw [← Submodule.Quotient.mk_smul] at he
        exact (show eU ⟨y, hy⟩ - α • (⟨y, hy⟩ : U) ∈ P from
          (Submodule.Quotient.eq P).mp he)
      · intro he
        have hd := congrArg (fun S : Submodule K M.carrier ↦ Module.finrank K S) he
        simp only [L, U, hdim, Fin.val_castSucc, Fin.val_succ] at hd
        omega
    have hα0 : α ≠ 0 := ne_zero_of_hasEigenvalue hαM
    have hpos : 0 < ‖iota α‖ := norm_pos_iff.mpr ((map_ne_zero iota).mpr hα0)
    have hqr : (1 : ℝ) < q := by exact_mod_cast hq
    let t : ℝ := 2 * Real.log ‖iota α‖ / Real.log q
    have htval : (q : ℝ) ^ (t / 2) = ‖iota α‖ := by
      rw [Real.rpow_def_of_pos (by linarith)]
      have he : Real.log q * (t / 2) = Real.log ‖iota α‖ := by
        dsimp [t]
        field_simp [(Real.log_pos hqr).ne']
      rw [he, Real.exp_log hpos]
    have htw : t ≤ w := by
      have he := (Real.rpow_le_rpow_left_iff hqr).mp (htval.le.trans (h α hαM))
      linarith
    refine ⟨t, G, htw, ?_, ?_⟩
    · intro y hy
      rfl
    · intro β hβ
      obtain ⟨y, hy⟩ := hβ.exists_hasEigenvector
      have hab : α = β := (smul_left_injective K hy.2)
        ((hscalar y).symm.trans hy.apply_eq_smul)
      rw [← hab]
      exact htval.symm

end FrobeniusModule
