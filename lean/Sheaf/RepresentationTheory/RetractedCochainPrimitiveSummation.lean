/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Completion

/-! # Summation of retracted continuous cochain primitives

Source: the agent-formulated scalar analytic input attached to paragraph (3) of the
latest Weil blueprint, six-functors direct-images proof, old primitive-descent steps
11--13. The blueprint supplies application context, not this auxiliary theorem;
an exact literature reference remains WANTED.
(blueprint: lem-sfb-retracted-cochain-primitive-summation).

Degree `n + 2` ranges over exactly the degrees at least two. The finite-evaluation
operators, retractions and selectors are the supplied ones. The witnesses `B` and `b`
are determined pointwise by their displayed formulas, and the completed limit is
explicitly the inclusion of a continuous map valued in the original space `V`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped BigOperators
open Filter UniformSpace

namespace ContinuousCohomology

/-- The existing continuous inhomogeneous differential for the trivial action on a
normed vector space, including the zero degree-zero differential.
Source: latest blueprint direct-images proof (3), agent scalar analytic expansion,
old primitive-descent steps 11--13
(blueprint: lem-sfb-retracted-cochain-primitive-summation). -/
noncomputable abbrev retractedTrivialD (l : ℕ) [Fact l.Prime]
    (V : Type u) [NormedAddCommGroup V] [NormedSpace ℚ_[l] V]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (r : ℕ) :=
  continuousInhomogeneousD (TopRep.of (ContRepresentation.trivial ℚ_[l] G V))
    continuous_snd r

/-- Retraction corrections of small cochain primitives have a pointwise finite,
uniformly convergent series whose continuous sum remains in the incomplete space.
Source: latest blueprint, six-functors direct-images proof (3), agent-formulated
scalar analytic input, old primitive-descent steps 11--13; reference WANTED
(blueprint: lem-sfb-retracted-cochain-primitive-summation).

Proof:
1. Write R_j h(s,x) = h(rho_j(s),x). The finite evaluation formula makes T_j h
   continuous. Retraction pullback is continuous and commutes with d, which changes
   only group coordinates. The differential is linear.
2. For j <= i, v = c_i - T_j e_i satisfies dv = 0 on A_j by the exactness hypothesis.
   Hence d(R_j v) = 0 and dB = d(T_j e_i) + dv - d(R_j v) = e_i. On A_j the
   retraction fixes s, so B(s,x) = T_j e_i(s,x).
3. Ultrametricity and the operator bound give norm(v(t,x)) <=
   max(norm(c_i), C_j * norm(e_i)). Rewrite B = c_i - R_j v and take suprema
   to obtain the same bound for B, with no factor two.
4. On each open fibre of k_i, b_i is one B_{i,j}, so it is continuous. Every face
   keeps s fixed, giving db_i = e_i. Since C_j <= D_i and D_i >= 1, the smallness
   hypothesis gives norm(b_i) <= 2^(-(i-1)). Also b_0 = c_0 and db_0 = e_0.
5. At fixed (s,x), eventually k_i(s) equals the least j with s in A_j. Thus b_i
   equals T_j e_i there. This is a fixed finite sum of evaluations of e_i, each
   eventually zero. Take the maximum of their thresholds, also when the list is empty.
6. Define b_* pointwise as the eventual constant partial sum, a finite sum in V.
   Every tail after N has norm <= 2^(-N) by ultrametricity, uniformly in (s,x).
7. Approximate b_* uniformly by a continuous finite partial sum. Its continuity
   and the strong triangle inequality prove continuity into the original norm topology.
8. By lem-sfb-metric-completion-isometry, the same error bound holds after the
   canonical inclusion into Completion V. Hence the completed series converges
   uniformly to that inclusion of b_*.
9. At fixed (s,y), choose a common stabilization threshold at the finitely many
   faces in d. There db_* equals the corresponding partial sum of e_i. Its assumed
   convergence to z in the completion, and the distance identity of
   lem-sfb-metric-completion-isometry, give norm(db_*(s,y) - z(s,y)) < epsilon for
   every epsilon > 0, hence db_* = z as actual V-valued cochains.
-/
theorem exists_retractedCochainPrimitiveSummation
    (l : ℕ) [Fact l.Prime] (V : Type u) [NormedAddCommGroup V]
    [NormedSpace ℚ_[l] V] (hultra : ∀ v w : V, ‖v + w‖ ≤ max ‖v‖ ‖w‖)
    (S : Type w) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S] [Nonempty S]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (n : ℕ)
    (A : ℕ+ → Set S) (hA : ∀ j : ℕ+, (A j).Nonempty ∧ IsClosed (A j))
    (hcover : ∀ s : S, ∃ j : ℕ+, s ∈ A j)
    (rho : ∀ j : ℕ+, C(S, A j)) (hrho : ∀ (j : ℕ+) (a : A j), rho j a = a)
    (k : ∀ i : ℕ+, LocallyConstant S {j : ℕ+ // j ≤ i})
    (hk : ∀ s : S, ∃ j : ℕ+, s ∈ A j ∧ (∀ q : ℕ+, s ∈ A q → j ≤ q) ∧
      ∀ᶠ i : ℕ+ in atTop, (k i s).val = j)
    (T : ℕ+ → C(S × (Fin (n + 2) → G), V) →ₗ[ℚ_[l]]
      C(S × (Fin (n + 1) → G), V))
    (uT : ℕ+ → ℕ) (alpha : ∀ j : ℕ+, Fin (uT j) → ℚ_[l])
    (psi : ∀ j : ℕ+, Fin (uT j) → C((Fin (n + 1) → G), (Fin (n + 2) → G)))
    (hT : ∀ (j : ℕ+) (h : C(S × (Fin (n + 2) → G), V))
      (s : S) (x : Fin (n + 1) → G),
      T j h (s, x) = ∑ a : Fin (uT j), alpha j a • h (s, psi j a x))
    (C : ℕ+ → ℝ) (hC : ∀ j : ℕ+, 1 ≤ C j)
    (hbound : ∀ (j : ℕ+) (h : C(S × (Fin (n + 2) → G), V)),
      ‖T j h‖ ≤ C j * ‖h‖)
    (e : ℕ → C(S × (Fin (n + 2) → G), V))
    (c : ℕ → C(S × (Fin (n + 1) → G), V))
    (he : ∀ (i : ℕ) (s : S), retractedTrivialD l V G (n + 2) ((e i).curry s) = 0)
    (hc : ∀ (i : ℕ) (s : S),
      retractedTrivialD l V G (n + 1) ((c i).curry s) = (e i).curry s)
    (hsmall : ∀ i : ℕ, 1 ≤ i → max ‖e i‖ ‖c i‖ ≤
      (2 : ℝ)⁻¹ ^ (i - 1) / max 1 (⨆ j : Fin i, C ⟨j.val + 1, Nat.succ_pos j.val⟩))
    (hevent : ∀ q : S × (Fin (n + 2) → G), ∀ᶠ i : ℕ in atTop, e i q = 0)
    (z : C(S × (Fin (n + 2) → G), V))
    (hz : TendstoUniformly
      (fun N q ↦ ((∑ i ∈ Finset.range (N + 1), e i q : V) : Completion V))
      (fun q ↦ (z q : Completion V)) atTop)
    (hexact : ∀ (i j : ℕ+), j ≤ i → ∀ a : A j,
      retractedTrivialD l V G (n + 1) ((T j (e i)).curry a) = (e i).curry a) :
    ∃ (B : ∀ i : ℕ+, {j : ℕ+ // j ≤ i} → C(S × (Fin (n + 1) → G), V))
      (b : ℕ → C(S × (Fin (n + 1) → G), V))
      (bStar : C(S × (Fin (n + 1) → G), V)),
      (∀ (i : ℕ+) (j : {j : ℕ+ // j ≤ i}) (s : S) (x : Fin (n + 1) → G),
        B i j (s, x) = T j.val (e i) (s, x) +
          (c i (s, x) - T j.val (e i) (s, x)) -
          (c i ((rho j.val s : S), x) - T j.val (e i) ((rho j.val s : S), x))) ∧
      b 0 = c 0 ∧
      (∀ (i : ℕ+) (s : S) (x : Fin (n + 1) → G), b i (s, x) = B i (k i s) (s, x)) ∧
      (∀ (i : ℕ+) (j : {j : ℕ+ // j ≤ i}) (s : S),
        retractedTrivialD l V G (n + 1) ((B i j).curry s) = (e i).curry s) ∧
      (∀ (i : ℕ+) (j : {j : ℕ+ // j ≤ i}) (s : S), s ∈ A j.val →
        ∀ x : Fin (n + 1) → G, B i j (s, x) = T j.val (e i) (s, x)) ∧
      (∀ (i : ℕ+) (j : {j : ℕ+ // j ≤ i}),
        ‖B i j‖ ≤ max ‖c i‖ (C j.val * ‖e i‖)) ∧
      (∀ (i : ℕ) (s : S),
        retractedTrivialD l V G (n + 1) ((b i).curry s) = (e i).curry s) ∧
      (∀ i : ℕ+, ‖b i‖ ≤ (2 : ℝ)⁻¹ ^ ((i : ℕ) - 1)) ∧
      (∀ q : S × (Fin (n + 1) → G), ∀ᶠ i : ℕ in atTop, b i q = 0) ∧
      TendstoUniformly
        (fun N q ↦ ((∑ i ∈ Finset.range (N + 1), b i q : V) : Completion V))
        (fun q ↦ (bStar q : Completion V)) atTop ∧
      ∀ s : S, retractedTrivialD l V G (n + 1) (bStar.curry s) = z.curry s := by
  sorry

end ContinuousCohomology
