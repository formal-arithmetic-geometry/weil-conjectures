/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeightsEmbedding
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.IsMixedOfWeightsAtMostEmbedding.FrobeniusEmbeddingExtensionBounds
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Punctual bounds give mixed Frobenius modules

Source: latest blueprint, `sk-thm-wft-affine-curve-upper.proof.md`, final paragraph,
filtration and spectral formulations used in quotient and constant-field descent
(blueprint: lem-a1-embedding-spectral-bounds).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace FrobeniusModule

private theorem mixed_of_pure
    {K : Type v} [Field K] (iota : K →+* ℂ) (q : ℕ) (M : FrobeniusModule.{u, v} K) (w t : ℝ)
    (ht : t ≤ w) (hM : M.IsPureOfWeight iota q t) :
    IsMixedOfWeightsAtMostEmbedding iota q M w := by
  classical
  let V : Fin 2 → Submodule K M.carrier := fun r ↦ if r = 0 then ⊥ else ⊤
  refine ⟨1, V, by simp [V], by simp [V], ?_, ?_, ?_⟩
  · intro r
    fin_cases r
    simp [V]
  · intro r
    fin_cases r <;> simp [V]
  · intro r
    fin_cases r
    change ∃ (t : ℝ) (G : _ ≃ₗ[K] _), _
    let P : Submodule K (⊤ : Submodule K M.carrier) :=
      (⊥ : Submodule K M.carrier).comap (⊤ : Submodule K M.carrier).subtype
    have hP : P = ⊥ := by ext x; simp [P]
    let e := (P.quotEquivOfEqBot hP).trans (Submodule.topEquiv :
      (⊤ : Submodule K M.carrier) ≃ₗ[K] M.carrier)
    let G := (e.trans M.frobenius).trans e.symm
    refine ⟨t, G, ht, ?_, ?_⟩
    · intro x hx
      apply e.injective
      simp [G, e, P, V]
    · apply hM.of_equiv
      refine ⟨e, ?_⟩
      intro x
      change e (e.symm (M.frobenius (e x))) = M.frobenius (e x)
      exact e.apply_symm_apply _

/-- A bound on every Frobenius eigenvalue gives a finite stable filtration with pure
successive quotients of weights at most `w`.

Source: latest blueprint, `sk-thm-wft-affine-curve-upper.proof.md`, final paragraph,
filtration construction for quotient and constant-field descent
(blueprint: lem-a1-embedding-spectral-bounds).

Proof: induct on the dimension. In positive dimension choose a nonzero eigenspace,
which is stable under Frobenius and its inverse. On it all eigenvalues equal alpha,
so give it weight 2 log |iota(alpha)| / log q; positivity and the spectral bound make
this a real weight at most w. Every eigenvalue on the quotient lifts to the original
module by equivariant surjective eigenvalue transfer. Its strictly smaller dimension
allows induction. Splice the pure eigenspace and mixed quotient filtrations using
the proved arbitrary-embedding extension lemma. In dimension zero, purity is vacuous. -/
private theorem mixed_of_bound
    {K : Type v} [Field K] [IsAlgClosed K]
    (iota : K →+* ℂ) (q : ℕ) (hq' : 1 < q) (M : FrobeniusModule.{u, v} K) (w : ℝ)
    (h : ∀ α : K, M.frobeniusEnd.HasEigenvalue α →
      ‖iota α‖ ≤ (q : ℝ) ^ (w / 2)) :
    IsMixedOfWeightsAtMostEmbedding iota q M w := by
  classical
  have hq : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq'
  induction hn : Module.finrank K M.carrier using Nat.strong_induction_on
      generalizing M with
  | h n ih =>
    by_cases hn0 : n = 0
    · have : Subsingleton M.carrier := (Module.finrank_zero_iff (R := K)).mp
        (hn.trans hn0)
      apply mixed_of_pure iota q M w w le_rfl
      intro α hα
      obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
      exact False.elim (hx.2 (Subsingleton.elim _ _))
    · have : Nontrivial M.carrier := (Module.finrank_pos_iff (R := K)).mp (by omega)
      obtain ⟨α, hα⟩ := M.frobeniusEnd.exists_eigenvalue
      have hα0 : α ≠ 0 := ne_zero_of_hasEigenvalue hα
      let S := M.frobeniusEnd.eigenspace α
      have hSact : ∀ x : M.carrier, x ∈ S → M.frobenius x = α • x :=
        fun x hx ↦ Module.End.mem_eigenspace_iff.mp hx
      have hS : S.map M.frobenius.toLinearMap = S := by
        apply le_antisymm
        · rintro _ ⟨x, hx, rfl⟩
          change M.frobenius x ∈ S
          rw [hSact x hx]
          exact S.smul_mem α hx
        · intro x hx
          refine ⟨α⁻¹ • x, S.smul_mem _ hx, ?_⟩
          change M.frobenius (α⁻¹ • x) = x
          rw [LinearEquiv.map_smul, hSact x hx, inv_smul_smul₀ hα0]
      let A : FrobeniusModule K :=
        { carrier := S
          frobenius := M.frobenius.ofSubmodules S S hS }
      let C : FrobeniusModule K :=
        { carrier := M.carrier ⧸ S
          frobenius := Submodule.Quotient.equiv S S M.frobenius hS }
      have hf : ∀ x : A.carrier, S.subtype (A.frobenius x) =
          M.frobenius (S.subtype x) := fun _ ↦ rfl
      have hg : ∀ x : M.carrier, S.mkQ (M.frobenius x) = C.frobenius (S.mkQ x) :=
        fun _ ↦ rfl
      have hdim : Module.finrank K C.carrier < n := by
        have hd := S.finrank_quotient_add_finrank
        have hp : 0 < Module.finrank K S :=
          Nat.succ_le_iff.mp (Submodule.one_le_finrank_iff.mpr hα)
        change Module.finrank K (M.carrier ⧸ S) < n
        omega
      have hC : IsMixedOfWeightsAtMostEmbedding iota q C w := by
        apply ih _ hdim C
        · intro β hβ
          exact h β (hasEigenvalue_of_surjective S.mkQ hg S.mkQ_surjective hβ)
        · rfl
      let t : ℝ := 2 * Real.log ‖iota α‖ / Real.log (q : ℝ)
      have hnα : 0 < ‖iota α‖ := norm_pos_iff.mpr ((map_ne_zero iota).mpr hα0)
      have hlog : Real.log (q : ℝ) ≠ 0 := (Real.log_pos hq).ne'
      have htval : (q : ℝ) ^ (t / 2) = ‖iota α‖ := by
        rw [Real.rpow_def_of_pos (by linarith)]
        have he : Real.log (q : ℝ) * (t / 2) = Real.log ‖iota α‖ := by
          dsimp [t]
          field_simp
        rw [he, Real.exp_log hnα]
      have htw : t ≤ w := by
        have he := (Real.rpow_le_rpow_left_iff hq).mp
          (htval.le.trans (h α hα))
        linarith
      have hApure : A.IsPureOfWeight iota q t := by
        intro β hβ
        obtain ⟨x, hx⟩ := hβ.exists_hasEigenvector
        have hx0 : (x : M.carrier) ≠ 0 := by
          intro he
          exact hx.2 (Subtype.ext he)
        have he : α • (x : M.carrier) = β • (x : M.carrier) := by
          have he := congrArg (fun y : S ↦ (y : M.carrier))
            (Module.End.mem_eigenspace_iff.mp hx.1)
          exact (hSact x x.2).symm.trans he
        have hab : α = β := (smul_left_injective K hx0) he
        rw [← hab]
        exact htval.symm
      exact IsMixedOfWeightsAtMostEmbedding.of_shortExact iota q
        A M C S.subtype S.mkQ hf hg Subtype.val_injective
        (LinearMap.exact_subtype_mkQ S) S.mkQ_surjective w
        (mixed_of_pure iota q A w t htw hApure) hC

private theorem bound_of_mixed
    {K : Type v} [Field K] (iota : K →+* ℂ) (q : ℕ) (hq' : 1 ≤ q)
    (M : FrobeniusModule.{u, v} K) (w : ℝ)
    (hM : IsMixedOfWeightsAtMostEmbedding iota q M w) :
    M.HasWeightsAtMost iota q w := by
  obtain ⟨m, V, hzero, hwhole, _, hstable, hpure⟩ := hM
  intro α hα
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  have hq : (1 : ℝ) ≤ (q : ℕ) := by
    exact_mod_cast hq'
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
  exact hfil (Fin.last m) x (by simp [hwhole]) hx.1 hx.2

/-- Over an algebraically closed field, a finite stable filtration with pure bounded
pieces is equivalent to the spectral upper bound, for any complex embedding and q > 1.

Source: latest blueprint, sk-thm-wft-affine-curve-upper, final paragraph: pass the
bound through the two quotients and descend the constant field.
(blueprint: lem-a1-embedding-spectral-bounds).

Proof: a nonzero eigenvector first occurs in some filtration piece, so its image in
that pure graded piece gives the spectral bound. Conversely take an eigenspace,
assign it the real weight 2 log |iota(alpha)| / log q, and induct on the dimension
of the quotient. The spectral bound passes to that quotient; splice its filtration
with the pure eigenspace filtration using the extension theorem. The zero vector
space is covered by a vacuous pure filtration. -/
theorem isMixedOfWeightsAtMostEmbedding_iff_hasWeightsAtMost
    {K : Type v} [Field K] [IsAlgClosed K] (iota : K →+* ℂ)
    (q : ℕ) (hq : 1 < q) (M : FrobeniusModule.{u, v} K) (w : ℝ) :
    IsMixedOfWeightsAtMostEmbedding iota q M w ↔ M.HasWeightsAtMost iota q w := by
  exact ⟨bound_of_mixed iota q (by omega) M w, mixed_of_bound iota q hq M w⟩

end FrobeniusModule
