/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Finite images of continuous profinite cochains

Source: blueprint latest, `sec-six-functors-basics/sk-lem-base-field-cd`,
opening paragraph of `sk-lem-base-field-cd-cochains.proof.md` (blueprint:
lem-sfb-cochain-finite-image).
-/

@[expose] public section

set_option autoImplicit false

universe u v

/-- A continuous cochain on a profinite group has finite image and is invariant under
coordinatewise right multiplication by one open normal subgroup.

Source: blueprint latest, `sec-six-functors-basics/sk-lem-base-field-cd`, opening paragraph of
`sk-lem-base-field-cd-cochains.proof.md` (blueprint: lem-sfb-cochain-finite-image).

Proof.

Step 1: the image of the compact space `G^n` is compact, and a compact subset of the
discrete space `S` is finite. For `n = 0`, take the whole group as `N`, since the domain
is a singleton.

Step 2: apply the existing source-library theorem
`ProfiniteGrp.exists_openNormalSubgroup_right_invariant` to the profinite group `G^n`.
It gives an open normal subgroup `U` of `G^n` preserving `f` under right multiplication.

Step 3: pull `U` back along each continuous coordinate inclusion `G → G^n`, and intersect
these finitely many open normal subgroups to obtain `N`. If every coordinate of `h`
belongs to `N`, each coordinate-singleton tuple belongs to `U`, so their product `h`
belongs to `U`. Right invariance under `U` gives `f (g * h) = f g`.
-/
theorem continuous_cochain_finite_image
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (n : ℕ) (S : Type v) [TopologicalSpace S] [DiscreteTopology S]
    (f : (Fin n → G) → S) (hf : Continuous f) :
    (Set.range f).Finite ∧
      ∃ N : OpenNormalSubgroup G,
        ∀ (g h : Fin n → G), (∀ i, h i ∈ N) → f (g * h) = f g := by
  classical
  refine ⟨(isCompact_range hf).finite_of_discrete, ?_⟩
  cases n with
  | zero =>
    refine ⟨⟨⊤, (show (⊤ : Subgroup G).Normal from inferInstance)⟩, ?_⟩
    intro g h _
    exact congrArg f (Subsingleton.elim _ _)
  | succ n =>
    obtain ⟨U, hU⟩ := ProfiniteGrp.exists_openNormalSubgroup_right_invariant
      (ProfiniteGrp.of (Fin (n + 1) → G)) S f hf
    let H (i : Fin (n + 1)) : OpenNormalSubgroup G :=
      { toOpenSubgroup := U.toOpenSubgroup.comap
          (MonoidHom.mulSingle (fun _ : Fin (n + 1) ↦ G) i) (continuous_mulSingle i)
        isNormal' := U.isNormal'.comap
          (MonoidHom.mulSingle (fun _ : Fin (n + 1) ↦ G) i) }
    let N : OpenNormalSubgroup G := Finset.univ.inf' Finset.univ_nonempty H
    refine ⟨N, ?_⟩
    intro g h hh
    apply hU g h
    apply Subgroup.pi_mem_of_mulSingle_mem
    intro i
    exact (Finset.inf'_le H (Finset.mem_univ i) : N ≤ H i) (hh i)

end
