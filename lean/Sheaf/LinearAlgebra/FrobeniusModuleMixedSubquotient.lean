/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic
import Sheaf.LinearAlgebra.FrobeniusPunctualBoundMixed

/-!
# Mixed weight bounds on Frobenius-stable subquotients

Source: Weil-conjectures blueprint, chapter `sec-deligne-laumon-a1`, unit
`sk-l-dl-a1-endpoints`, node `lem-a1-subquotient-extension-bounds`
(blueprint: lem-a1-subquotient-extension-bounds).

The subquotient is `S ⧸ U`, where `S` is a stable subspace of the ambient module
and `U` is a stable subspace of `S`. Its Frobenius is the canonical restriction
followed by the canonical quotient automorphism from Mathlib.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace FrobeniusModule

/-- Every Frobenius-stable subquotient of a module mixed of weights at most `w`
is mixed of weights at most `w`, with the same prime power and coefficient isomorphism.

Source: Weil-conjectures blueprint, chapter `sec-deligne-laumon-a1`, unit
`sk-l-dl-a1-endpoints`, node `lem-a1-subquotient-extension-bounds`
(blueprint: lem-a1-subquotient-extension-bounds).

Proof: follow a nonzero eigenvector through the finite stable filtration supplied by
`def-weil-frobenius-module-weights`. Induction on the filtration index either places it
in the preceding piece or gives a nonzero eigenvector in the next pure quotient.
Purity bounds its iota-modulus by `(p ^ a) ^ (w / 2)`, using monotonicity of real powers.
The subtype inclusion transfers this ambient bound to `S`. The canonical surjection
`S → S ⧸ U` intertwines Frobenius, so
`Module.End.hasEigenvalue_of_comp_eq_comp` transfers each quotient eigenvalue to `S`.
Finally `lem-a1-punctual-bound-module-mixed` converts the quotient eigenvalue bound
into the required finite mixed filtration. No stable complement or semisimplicity is
needed, and the argument includes zero modules and `U = S`. -/
theorem IsMixedOfWeightsAtMost.subquotient
    (p a ell : ℕ) [Fact (Nat.Prime p)] (ha : 1 ≤ a)
    [Fact (Nat.Prime ell)] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra (ℚ_[ell]) Qlb] (hQ : IsAlgClosure (ℚ_[ell]) Qlb)
    (iota : Qlb ≃+* ℂ) (M : FrobeniusModule.{u, v} Qlb) (w : ℝ)
    (hM : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota M w)
    (S : Submodule Qlb M.carrier) (hS : S.map M.frobenius.toLinearMap = S)
    (U : Submodule Qlb S)
    (hU : U.map (M.frobenius.ofSubmodules S S hS).toLinearMap = U) :
    IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota
      { carrier := S ⧸ U
        frobenius := Submodule.Quotient.equiv U U (M.frobenius.ofSubmodules S S hS) hU } w := by
  classical
  have hbound : M.HasWeightsAtMost (iota : Qlb →+* ℂ) (p ^ a) w := by
    obtain ⟨m, V, hzero, hwhole, _, hstable, hpure⟩ := hM
    intro α hα
    obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    have hq : (1 : ℝ) ≤ (p ^ a : ℕ) := by
      exact_mod_cast one_le_pow₀ (Fact.out : Nat.Prime p).one_le
    have hfil : ∀ r : Fin (m + 1), ∀ y : M.carrier,
        y ∈ V r → M.frobenius y = α • y → y ≠ 0 →
        ‖iota α‖ ≤ ((p ^ a : ℕ) : ℝ) ^ (w / 2) := by
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
            have hnorm : ‖iota α‖ = ((p ^ a : ℕ) : ℝ) ^ (wr / 2) := hp α heig
            exact hnorm.le.trans (Real.rpow_le_rpow_of_exponent_le hq
              (div_le_div_of_nonneg_right hwr (by norm_num)))
    exact hfil ⟨m, Nat.lt_succ_self m⟩ x (by simp [hwhole]) hx.1 hx.2
  let N : FrobeniusModule Qlb :=
    { carrier := S
      frobenius := M.frobenius.ofSubmodules S S hS }
  have hN : N.HasWeightsAtMost (iota : Qlb →+* ℂ) (p ^ a) w := by
    intro α hα
    apply hbound α
    obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := (x : M.carrier))
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨congrArg Subtype.val hx.1, fun h ↦ hx.2 (Subtype.ext h)⟩
  apply isMixedOfWeightsAtMost_of_forall_hasEigenvalue p a ell ha hellp Qlb hQ iota
  intro α hα
  apply hN α
  exact Module.End.hasEigenvalue_of_comp_eq_comp N.frobeniusEnd _ U.mkQ
    (Submodule.mkQ_surjective U) (by ext; rfl) hα

end FrobeniusModule
