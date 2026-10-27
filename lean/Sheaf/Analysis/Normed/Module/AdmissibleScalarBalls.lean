/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Compactness.Compact

/-! # A common admissible scalar from compact ultrametric balls

Source: Weil blueprint, sec-six-functors-basics,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), scalar tame-kernel
finite-field projection input (blueprint: lem-sfb-admissible-scalar-balls).
This is the agent-formulated compact admissible-ball selection auxiliary; the
external Ingleton scalar-extension reference remains WANTED in the DAG source.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace LinearMap

/-- A contractive linear functional on a subspace admits a scalar satisfying all
the ball constraints for extension at one vector outside the subspace.

Source: Weil blueprint, sec-six-functors-basics,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), compact admissible-ball
selection (blueprint: lem-sfb-admissible-scalar-balls). The following proof is the
agent-formulated argument recorded in the DAG, not a proof present in the blueprint.

Proof:
1. Multiplicativity and nonnegativity imply |-1| = 1, hence |-a| = |a| and
   ‖-v‖ = ‖v‖. The induced distance is a metric: symmetry follows from these
   identities, separation from the zero-norm axiom, and the triangle inequality
   from the ultrametric inequality and max(s,t) ≤ s+t for nonnegative s,t.
   Linearity gives g(0) = 0 and g(u)-g(w) = g(u-w).
2. Put c_u = g(u), r_u = ‖x-u‖ and B_u = {b | |b-c_u| ≤ r_u}. Each radius is
   nonnegative and each ball contains its center. The bound on g gives
   |c_u-c_w| ≤ ‖u-w‖ ≤ max(r_u,r_w), by writing u-w = (u-x)+(x-w).
3. If r_u ≤ r_w and b ∈ B_u, the scalar ultrametric inequality gives
   |b-c_w| ≤ max(|b-c_u|,|c_u-c_w|) ≤ r_w. Thus B_u ⊆ B_w. For a finite set F
   of indices choose w of least radius in F ∪ {0}; its center lies in B_0 and
   every B_u indexed by F. This includes F empty, using w = 0.
4. Each B_u is closed. Indeed, for a outside B_u let h = |a-c_u| > r_u.
   If dist(a,z) < h and z ∈ B_u, the ultrametric inequality would give
   h ≤ max(dist(a,z),r_u) < h. The open ball of radius h around a therefore
   avoids B_u. No positive lower bound on the radii is required.
5. The hypothesis makes B_0 compact. On its subspace topology, the sets
   C_u = B_0 ∩ B_u are closed and have nonempty finite intersections by step 3;
   the empty intersection contains 0. Apply lem-sfb-compact-closed-finite-intersection
   (Mathlib's CompactSpace.iInter_nonempty, Stacks Tag 005D) to obtain a point in
   every C_u. Its underlying scalar b satisfies every asserted inequality.
-/
theorem exists_admissible_scalar_of_isCompact_closedBall
    {K : Type u} [NormedField K]
    (hK : ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    {V : Type v} [NormedAddCommGroup V] [NormedSpace K V]
    (hV : ∀ y z : V, ‖y + z‖ ≤ max ‖y‖ ‖z‖)
    (hcompact : ∀ (a : K) (r : ℝ), 0 ≤ r → IsCompact (Metric.closedBall a r))
    (U : Submodule K V) (g : U →ₗ[K] K)
    (hg : ∀ u : U, ‖g u‖ ≤ ‖(u : V)‖) (x : V) (hx : x ∉ U) :
    ∃ b : K, ∀ u : U, ‖b - g u‖ ≤ ‖x - (u : V)‖ := by
  have _ := hx
  let B : U → Set K := fun u ↦ Metric.closedBall (g u) ‖x - (u : V)‖
  have hcent (u w : U) : ‖g u - g w‖ ≤ max ‖x - (u : V)‖ ‖x - (w : V)‖ := by
    calc
      ‖g u - g w‖ = ‖g (u - w)‖ := by rw [map_sub]
      _ ≤ ‖((u - w : U) : V)‖ := hg (u - w)
      _ = ‖((u : V) - x) + (x - (w : V))‖ := by
        simp only [Submodule.coe_sub, sub_add_sub_cancel]
      _ ≤ max ‖(u : V) - x‖ ‖x - (w : V)‖ := hV _ _
      _ = max ‖x - (u : V)‖ ‖x - (w : V)‖ := by rw [norm_sub_rev (u : V) x]
  have hsub (u w : U) (huw : ‖x - (u : V)‖ ≤ ‖x - (w : V)‖) : B u ⊆ B w := by
    intro b hb
    simp only [B, Metric.mem_closedBall, dist_eq_norm] at hb ⊢
    calc
      ‖b - g w‖ = ‖(b - g u) + (g u - g w)‖ := by rw [sub_add_sub_cancel]
      _ ≤ max ‖b - g u‖ ‖g u - g w‖ := hK _ _
      _ ≤ ‖x - (w : V)‖ := max_le (hb.trans huw)
        ((hcent u w).trans (max_le huw le_rfl))
  have hdir : Directed (· ⊇ ·) B := by
    intro u w
    rcases le_total ‖x - (u : V)‖ ‖x - (w : V)‖ with huw | hwu
    · exact ⟨u, Set.Subset.rfl, hsub u w huw⟩
    · exact ⟨w, hsub w u hwu, Set.Subset.rfl⟩
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed B
    hdir (fun u ↦ ⟨g u, by simp [B]⟩)
    (fun u ↦ hcompact (g u) ‖x - (u : V)‖ (norm_nonneg _))
    (fun _ ↦ Metric.isClosed_closedBall)
  refine ⟨b, fun u ↦ ?_⟩
  simpa only [B, Metric.mem_closedBall, dist_eq_norm] using Set.mem_iInter.mp hb u

end LinearMap
