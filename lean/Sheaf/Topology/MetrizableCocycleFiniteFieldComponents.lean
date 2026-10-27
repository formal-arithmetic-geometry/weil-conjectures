/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Tactic.Linarith
import Sheaf.Topology.ProfiniteMetricFunctionQuotients
import Sheaf.NumberTheory.Padics.CountableClosedFiniteCover
import Sheaf.NumberTheory.Padics.NormOneFiniteSubfieldProjection

/-! # Metrizable descent and finite-field components of continuous scalar cocycles

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent-formulated analytic lemma
(blueprint: lem-sfb-metrizable-cocycle-finite-field-components).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Filter Topology

namespace Profinite

/-- A continuous scalar cocycle admits metrizable profinite quotients and finite-field
components with the stated pointwise and uniform convergence properties.

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent-formulated analytic lemma
(blueprint: lem-sfb-metrizable-cocycle-finite-field-components).

Proof:
1. Apply `Profinite.exists_metrizable_quotients_factorization` to the metric-valued
   cocycle.  The factorization preserves the cocycle equation by surjectivity, and every
   finite quotient of the quotient group pulls back along the quotient homomorphism.
2. Apply `Padic.exists_monotone_closed_finiteIntermediateField_cover` to obtain the
   increasing closed finite intermediate fields exhausting the algebraic closure.  Apply
   `Padic.exists_normOne_finiteSubfield_projection` at each stage and set the zeroth
   predecessor to zero.
3. The differences of consecutive projections are continuous finite-field-valued
   cocycles.  Exhaustion makes every fixed value eventually fixed by both projections,
   giving pointwise eventual vanishing; telescoping gives the finite-sum identity.
4. The quotient domain is compact by `Pi.compactSpace` and compactness of products.
   If it is empty all sup norms vanish. Otherwise cover it by inverse images under z₀
   of epsilon/2-balls centered at its values. A finite subcover has centers in one F_J.
   For i ≥ J, the projections fix those centers. Contractivity and the ultrametric
   inequality bound each error by epsilon/2, uniformly on the domain. A finite cover
   with radius one also bounds all values, errors and components.
5. Finite telescoping gives the partial-sum identity. The norm of each positive-index
   component is bounded by the maximum of the two consecutive error norms, which tends
   to zero. Only the individual contraction and fixing properties were used, so the
   projections need not commute. No completeness of Ω or nonemptiness of S is required.
-/
theorem exists_metrizable_cocycle_finite_field_components
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [IsUltrametricDist Ω]
    (E : IntermediateField (Padic l) Ω) [FiniteDimensional (Padic l) E]
    (S : Profinite.{v}) (K : ProfiniteGrp.{v}) (n : ℕ) (hn : 1 ≤ n)
    (z : C(S × (Fin n → K), Ω))
    (hz : ∀ (s : S) (g : Fin (n + 1) → K),
      z (s, fun j ↦ g j.succ) +
          (∑ a : Fin n, (-1 : ℤ) ^ (a.val + 1) •
            z (s, Fin.contractNth a.castSucc (· * ·) g)) +
          (-1 : ℤ) ^ (n + 1) • z (s, fun j ↦ g j.castSucc) = 0) :
    ∃ (S₀ : Profinite.{v}) (G : ProfiniteGrp.{v}),
      TopologicalSpace.MetrizableSpace S₀ ∧
      TopologicalSpace.MetrizableSpace G ∧
      ∃ (p : C(S, S₀)) (q : K →ₜ* G)
        (z₀ : C(S₀ × (Fin n → G), Ω)),
        Function.Surjective p ∧ Function.Surjective q ∧
        (∀ (s : S) (g : Fin n → K),
          z (s, g) = z₀ (p s, fun j ↦ q (g j))) ∧
        (∀ (H : ProfiniteGrp.{v}) [Finite H] (h : G →ₜ* H),
          Function.Surjective h → Function.Surjective (h.comp q)) ∧
        (∀ (s : S₀) (g : Fin (n + 1) → G),
          z₀ (s, fun j ↦ g j.succ) +
              (∑ a : Fin n, (-1 : ℤ) ^ (a.val + 1) •
                z₀ (s, Fin.contractNth a.castSucc (· * ·) g)) +
              (-1 : ℤ) ^ (n + 1) • z₀ (s, fun j ↦ g j.castSucc) = 0) ∧
        ∃ (F : ℕ → IntermediateField (Padic l) Ω)
          (pᵢ : ∀ i : ℕ, Ω →L[F i] F i)
          (e : ∀ i : ℕ, C(S₀ × (Fin n → G), F i)),
          Monotone F ∧
          (∀ i : ℕ, E ≤ F i ∧ FiniteDimensional (Padic l) (F i) ∧
            IsClosed (F i : Set Ω)) ∧
          (⋃ i : ℕ, (F i : Set Ω)) = Set.univ ∧
          (∀ (i : ℕ) (a : F i), pᵢ i (a : Ω) = a) ∧
          (∀ (i : ℕ) (x : Ω), ‖pᵢ i x‖ ≤ ‖x‖) ∧
          (∀ (i : ℕ) (s : S₀) (g : Fin (n + 1) → G),
            e i (s, fun j ↦ g j.succ) +
                (∑ a : Fin n, (-1 : ℤ) ^ (a.val + 1) •
                  e i (s, Fin.contractNth a.castSucc (· * ·) g)) +
                (-1 : ℤ) ^ (n + 1) • e i (s, fun j ↦ g j.castSucc) = 0) ∧
          (∀ (i : ℕ) (t : S₀ × (Fin n → G)),
            ((e i) t : Ω) = (pᵢ i (z₀ t) : Ω) -
              if i = 0 then 0 else (pᵢ (i - 1) (z₀ t) : Ω)) ∧
          TendstoUniformly
            (fun i t ↦ ((pᵢ i (z₀ t) : F i) : Ω)) z₀ atTop ∧
          Tendsto (fun i ↦ ‖e i‖) atTop (𝓝 0) ∧
          (∀ (t : S₀ × (Fin n → G)), ∀ᶠ i : ℕ in atTop, e i t = 0) ∧
          (∀ (N : ℕ) (t : S₀ × (Fin n → G)),
            ∑ k ∈ Finset.range (N + 1), ((e k t : F k) : Ω) =
              (pᵢ N (z₀ t) : Ω)) := by
  classical
  obtain ⟨S₀, G, hS₀, hG, p, q, z₀, hp, hq, hfac⟩ :=
    exists_metrizable_quotients_factorization S K n hn Ω z
  have hz₀ (s : S₀) (g : Fin (n + 1) → G) :
      z₀ (s, fun j ↦ g j.succ) +
          (∑ a : Fin n, (-1 : ℤ) ^ (a.val + 1) •
            z₀ (s, Fin.contractNth a.castSucc (· * ·) g)) +
          (-1 : ℤ) ^ (n + 1) • z₀ (s, fun j ↦ g j.castSucc) = 0 := by
    obtain ⟨s, rfl⟩ := hp s
    choose k hk using fun j ↦ hq (g j)
    have htail : (fun j : Fin n ↦ q (k j.succ)) = (fun j ↦ g j.succ) :=
      funext fun j ↦ hk j.succ
    have hhead : (fun j : Fin n ↦ q (k j.castSucc)) = (fun j ↦ g j.castSucc) :=
      funext fun j ↦ hk j.castSucc
    have hface (a : Fin n) :
        (fun j ↦ q (Fin.contractNth a.castSucc (· * ·) k j)) =
          Fin.contractNth a.castSucc (· * ·) g := by
      calc
        _ = Fin.contractNth a.castSucc (· * ·) (fun j ↦ q (k j)) :=
          Fin.comp_contractNth (· * ·) (· * ·) (map_mul q) a.castSucc k
        _ = _ := by rw [show (fun j ↦ q (k j)) = g from funext hk]
    have h := hz s k
    simp only [hfac, htail, hhead, hface] at h
    exact h
  refine ⟨S₀, G, hS₀, hG, p, q, z₀, hp, hq, fun s g ↦ hfac (s, g), ?_, hz₀, ?_⟩
  · intro H _ h hh
    exact hh.comp hq
  obtain ⟨F, hmono, hF, hcover⟩ :=
    Padic.exists_monotone_closed_finiteIntermediateField_cover l Ω E
  have hproj (i : ℕ) : ∃ pᵢ : Ω →L[F i] F i,
      (∀ a : F i, pᵢ (a : Ω) = a) ∧ ∀ x : Ω, ‖pᵢ x‖ ≤ ‖x‖ := by
    have := (hF i).2.1
    exact Padic.exists_normOne_finiteSubfield_projection l Ω (F i)
  choose pᵢ hfix hbound using hproj
  let P (i : ℕ) : Ω →+ Ω := (F i).val.toAddMonoidHom.comp (pᵢ i).toAddMonoidHom
  have hPcont (i : ℕ) : Continuous (P i) :=
    continuous_subtype_val.comp (pᵢ i).continuous
  have hPmem (i : ℕ) (x : Ω) : P i x ∈ F i := (pᵢ i x).property
  have hPfix (i : ℕ) (x : Ω) (hx : x ∈ F i) : P i x = x :=
    congrArg Subtype.val (hfix i ⟨x, hx⟩)
  have hPbound (i : ℕ) (x : Ω) : ‖P i x‖ ≤ ‖x‖ := hbound i x
  have hfixed (x : Ω) : ∀ᶠ i : ℕ in atTop, P i x = x := by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ j, (F j : Set Ω) by rw [hcover]; trivial)
    filter_upwards [eventually_ge_atTop j] with i hi
    exact hPfix i x (hmono hi hj)
  let A (i : ℕ) : Ω →+ Ω := P i - if i = 0 then 0 else P (i - 1)
  have hAcont (i : ℕ) : Continuous (A i) := by
    by_cases hi : i = 0
    · simpa [A, hi] using hPcont 0
    · change Continuous (fun x ↦ A i x)
      simpa only [A, if_neg hi, AddMonoidHom.sub_apply] using
        (hPcont i).fun_sub (hPcont (i - 1))
  have hAmem (i : ℕ) (x : Ω) : A i x ∈ F i := by
    by_cases hi : i = 0
    · simpa [A, hi] using hPmem 0 x
    · simpa [A, hi] using
        (F i).sub_mem (hPmem i x) (hmono (Nat.sub_le i 1) (hPmem (i - 1) x))
  let e (i : ℕ) : C(S₀ × (Fin n → G), F i) :=
    ⟨fun t ↦ ⟨A i (z₀ t), hAmem i (z₀ t)⟩,
      ((hAcont i).comp z₀.continuous).subtype_mk _⟩
  have heval (i : ℕ) (t : S₀ × (Fin n → G)) :
      (e i t : Ω) = P i (z₀ t) - if i = 0 then 0 else P (i - 1) (z₀ t) := by
    by_cases hi : i = 0 <;> simp [e, A, hi]
  have hcocycle (i : ℕ) (s : S₀) (g : Fin (n + 1) → G) :
      e i (s, fun j ↦ g j.succ) +
          (∑ a : Fin n, (-1 : ℤ) ^ (a.val + 1) •
            e i (s, Fin.contractNth a.castSucc (· * ·) g)) +
          (-1 : ℤ) ^ (n + 1) • e i (s, fun j ↦ g j.castSucc) = 0 := by
    apply (F i).val.injective
    simp only [map_add, map_sum, map_zsmul, map_zero]
    change A i (z₀ (s, fun j ↦ g j.succ)) +
        (∑ a : Fin n, (-1 : ℤ) ^ (a.val + 1) •
          A i (z₀ (s, Fin.contractNth a.castSucc (· * ·) g))) +
        (-1 : ℤ) ^ (n + 1) • A i (z₀ (s, fun j ↦ g j.castSucc)) = 0
    simpa only [map_add, map_sum, map_zsmul, map_zero] using congrArg (A i) (hz₀ s g)
  have huniform : TendstoUniformly (fun i t ↦ P i (z₀ t)) z₀ atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    let U (a : S₀ × (Fin n → G)) : Set (S₀ × (Fin n → G)) :=
      {t | ‖z₀ t - z₀ a‖ < ε / 3}
    have hU (a) : IsOpen (U a) :=
      isOpen_lt (z₀.continuous.sub continuous_const).norm continuous_const
    have hcoverU : Set.univ ⊆ ⋃ a, U a := by
      intro t _
      exact Set.mem_iUnion.mpr ⟨t, by simp [U, hε]⟩
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hU hcoverU
    have hTfix : ∀ᶠ i : ℕ in atTop, ∀ a ∈ T, P i (z₀ a) = z₀ a :=
      (T.eventually_all).mpr fun a _ ↦ hfixed (z₀ a)
    filter_upwards [hTfix] with i hi t
    obtain ⟨a, ha, hta⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ t))
    have hta : ‖z₀ t - z₀ a‖ < ε / 3 := hta
    have herror : P i (z₀ t) - z₀ t =
        P i (z₀ t - z₀ a) - (z₀ t - z₀ a) := by
      rw [map_sub, hi a ha]
      abel
    rw [dist_comm, dist_eq_norm, herror]
    have hb := (norm_sub_le (P i (z₀ t - z₀ a)) (z₀ t - z₀ a)).trans
      (add_le_add (hPbound i (z₀ t - z₀ a)) le_rfl)
    linarith
  let c (i : ℕ) : C(S₀ × (Fin n → G), Ω) :=
    ⟨fun t ↦ P i (z₀ t), (hPcont i).comp z₀.continuous⟩
  have hc : Tendsto c atTop (𝓝 z₀) :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mpr huniform
  have hdiff : Tendsto (fun i ↦ c i - c (i - 1)) atTop (𝓝 0) := by
    simpa using hc.sub (hc.comp (tendsto_sub_atTop_nat 1))
  have hnorm : Tendsto (fun i ↦ ‖e i‖) atTop (𝓝 0) := by
    have hn : Tendsto (fun i ↦ ‖c i - c (i - 1)‖) atTop (𝓝 0) := by
      simpa using hdiff.norm
    apply hn.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with i hi
    simp only [ContinuousMap.norm_eq_iSup_norm]
    congr 1
    funext t
    change ‖P i (z₀ t) - P (i - 1) (z₀ t)‖ = ‖A i (z₀ t)‖
    simp [A, hi]
  have hzero (t : S₀ × (Fin n → G)) : ∀ᶠ i : ℕ in atTop, e i t = 0 := by
    filter_upwards [hfixed (z₀ t), (tendsto_sub_atTop_nat 1).eventually (hfixed (z₀ t)),
      eventually_ne_atTop (0 : ℕ)] with i hi hiprev hne
    apply Subtype.val_injective
    change A i (z₀ t) = 0
    simp [A, hne, hi, hiprev]
  have hsum (N : ℕ) (t : S₀ × (Fin n → G)) :
      ∑ k ∈ Finset.range (N + 1), ((e k t : F k) : Ω) = P N (z₀ t) := by
    induction N with
    | zero => simp [heval]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, heval]
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      rw [← add_sub_assoc, add_comm, add_sub_cancel_right]
  exact ⟨F, pᵢ, e, hmono, hF, hcover, hfix, hbound, hcocycle, heval,
    huniform, hnorm, hzero, hsum⟩

end Profinite
