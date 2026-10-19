/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Punctual bounds give mixed Frobenius modules

Source: Weil-conjectures blueprint, chapter `sec-deligne-laumon-a1`, unit
`sk-thm-dl-a1-upper`, lemma `lem-a1-punctual-bound-module-mixed`
(blueprint: lem-a1-punctual-bound-module-mixed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace FrobeniusModule

private theorem mixed_of_pure
    (p a ell : ℕ) [Fact (Nat.Prime p)] (ha : 1 ≤ a)
    [Fact (Nat.Prime ell)] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra (ℚ_[ell]) Qlb] (hQ : IsAlgClosure (ℚ_[ell]) Qlb)
    (iota : Qlb ≃+* ℂ) (M : FrobeniusModule.{u, v} Qlb) (w t : ℝ)
    (ht : t ≤ w) (hM : M.IsPureOfWeight iota.toRingHom (p ^ a) t) :
    IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota M w := by
  classical
  let V : Fin 2 → Submodule Qlb M.carrier := fun r => if r = 0 then ⊥ else ⊤
  refine ⟨1, V, by simp [V], by simp [V], ?_, ?_, ?_⟩
  · intro r
    fin_cases r
    simp [V]
  · intro r
    fin_cases r <;> simp [V]
  · intro r
    fin_cases r
    change ∃ (t : ℝ) (G : _ ≃ₗ[Qlb] _), _
    let P : Submodule Qlb (⊤ : Submodule Qlb M.carrier) :=
      (⊥ : Submodule Qlb M.carrier).comap (⊤ : Submodule Qlb M.carrier).subtype
    have hP : P = ⊥ := by ext x; simp [P]
    let e := (P.quotEquivOfEqBot hP).trans (Submodule.topEquiv :
      (⊤ : Submodule Qlb M.carrier) ≃ₗ[Qlb] M.carrier)
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

Source: Weil-conjectures blueprint, `sec-deligne-laumon-a1/sk-thm-dl-a1-upper`,
`lem-a1-punctual-bound-module-mixed`
(blueprint: lem-a1-punctual-bound-module-mixed).

Proof: choose a Jordan–Holder filtration of the finite-dimensional Frobenius module.
Every nonzero simple quotient is one-dimensional: over the algebraically closed coefficient
field it has an eigenvector, whose span is a nonzero stable subspace, hence is the whole
simple quotient. By `lem-a1-spectrum-exact-sequence`, the single eigenvalue of each quotient
is an eigenvalue of the original Frobenius, so its complex norm is at most `q ^ (w / 2)`.
The eigenvalue is nonzero because Frobenius is invertible. Since `q = p ^ a > 1`, assign this
quotient the real weight `2 * log (norm (iota eigenvalue)) / log q`; the bound implies that
this weight is at most `w`, and the quotient is pure of that weight by
`def-weil-frobenius-module-weights`. These quotients and their induced automorphisms exhibit
the required mixed filtration. For the zero module use the length-zero filtration. -/
theorem isMixedOfWeightsAtMost_of_forall_hasEigenvalue
    (p a ell : ℕ) [Fact (Nat.Prime p)] (ha : 1 ≤ a)
    [Fact (Nat.Prime ell)] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra (ℚ_[ell]) Qlb] (hQ : IsAlgClosure (ℚ_[ell]) Qlb)
    (iota : Qlb ≃+* ℂ) (M : FrobeniusModule.{u, v} Qlb) (w : ℝ)
    (h : ∀ α : Qlb, M.frobeniusEnd.HasEigenvalue α →
      ‖iota α‖ ≤ ((p ^ a : ℕ) : ℝ) ^ (w / 2)) :
    IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota M w := by
  classical
  have : IsAlgClosed Qlb := hQ.isAlgClosed
  have hq : (1 : ℝ) < ((p ^ a : ℕ) : ℝ) := by
    exact_mod_cast one_lt_pow₀ (Fact.out : Nat.Prime p).one_lt (by omega : a ≠ 0)
  induction hn : Module.finrank Qlb M.carrier using Nat.strong_induction_on
      generalizing M with
  | h n ih =>
    by_cases hn0 : n = 0
    · have : Subsingleton M.carrier := (Module.finrank_zero_iff (R := Qlb)).mp
        (hn.trans hn0)
      apply mixed_of_pure p a ell ha hellp Qlb hQ iota M w w le_rfl
      intro α hα
      obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
      exact False.elim (hx.2 (Subsingleton.elim _ _))
    · have : Nontrivial M.carrier := (Module.finrank_pos_iff (R := Qlb)).mp (by omega)
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
      let A : FrobeniusModule Qlb :=
        { carrier := S
          frobenius := M.frobenius.ofSubmodules S S hS }
      let C : FrobeniusModule Qlb :=
        { carrier := M.carrier ⧸ S
          frobenius := Submodule.Quotient.equiv S S M.frobenius hS }
      have hf : ∀ x : A.carrier, S.subtype (A.frobenius x) =
          M.frobenius (S.subtype x) := fun _ ↦ rfl
      have hg : ∀ x : M.carrier, S.mkQ (M.frobenius x) = C.frobenius (S.mkQ x) :=
        fun _ ↦ rfl
      have hdim : Module.finrank Qlb C.carrier < n := by
        have hd := S.finrank_quotient_add_finrank
        have hp : 0 < Module.finrank Qlb S :=
          Nat.succ_le_iff.mp (Submodule.one_le_finrank_iff.mpr hα)
        change Module.finrank Qlb (M.carrier ⧸ S) < n
        omega
      have hC : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota C w := by
        apply ih _ hdim C
        · intro β hβ
          exact h β (hasEigenvalue_of_surjective S.mkQ hg S.mkQ_surjective hβ)
        · rfl
      let t : ℝ := 2 * Real.log ‖iota α‖ / Real.log ((p ^ a : ℕ) : ℝ)
      have hnα : 0 < ‖iota α‖ := norm_pos_iff.mpr ((map_ne_zero iota).mpr hα0)
      have hlog : Real.log ((p ^ a : ℕ) : ℝ) ≠ 0 := (Real.log_pos hq).ne'
      have htval : ((p ^ a : ℕ) : ℝ) ^ (t / 2) = ‖iota α‖ := by
        rw [Real.rpow_def_of_pos (by linarith)]
        have he : Real.log ((p ^ a : ℕ) : ℝ) * (t / 2) = Real.log ‖iota α‖ := by
          dsimp [t]
          field_simp
        rw [he, Real.exp_log hnα]
      have htw : t ≤ w := by
        have he := (Real.rpow_le_rpow_left_iff hq).mp
          (htval.le.trans (h α hα))
        linarith
      have hApure : A.IsPureOfWeight iota.toRingHom (p ^ a) t := by
        intro β hβ
        obtain ⟨x, hx⟩ := hβ.exists_hasEigenvector
        have hx0 : (x : M.carrier) ≠ 0 := by
          intro he
          exact hx.2 (Subtype.ext he)
        have he : α • (x : M.carrier) = β • (x : M.carrier) := by
          have he := congrArg (fun y : S ↦ (y : M.carrier))
            (Module.End.mem_eigenspace_iff.mp hx.1)
          exact (hSact x x.2).symm.trans he
        have hab : α = β := (smul_left_injective Qlb hx0) he
        rw [← hab]
        exact htval.symm
      exact IsMixedOfWeightsAtMost.of_shortExact p a ell ha hellp Qlb hQ iota
        A M C S.subtype S.mkQ hf hg Subtype.val_injective
        (LinearMap.exact_subtype_mkQ S) S.mkQ_surjective w
        (mixed_of_pure p a ell ha hellp Qlb hQ iota A w t htw hApure) hC

end FrobeniusModule
