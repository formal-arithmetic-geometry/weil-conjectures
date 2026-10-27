/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.CategoryTheory.FiniteContinuousModule
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Surjectivity detected by restriction of finite continuous actions

Source: Stacks Project, Tag 0BN6, `lemma-functoriality-galois-surjective`,
equivalence of (1) and (2) (blueprint: lem-dl-a1-profinite-restriction-full-faithful).
-/

@[expose] public section

universe u v w

open CategoryTheory
open scoped Topology FintypeCatDiscrete

namespace ContAction

/-- A continuous homomorphism of profinite groups is onto exactly when restriction
of finite discrete continuous actions induces bijections on every morphism set.
Source: Stacks Project, Tag 0BN6, `lemma-functoriality-galois-surjective`, (1) iff (2)
(blueprint: lem-dl-a1-profinite-restriction-full-faithful).

Proof:
1. Restriction is the identity on underlying functions, hence faithful. If `h` is
   onto, lift each element of `G` to `H` to see that every `H`-equivariant function
   between restricted actions is `G`-equivariant. This includes empty actions.
2. Conversely, the image `K = h(H)` is closed by
   `lem-dl-a1-compact-hausdorff-closed-map`. If `g` lies outside `K`, choose an open
   normal subgroup `N` contained in the identity neighbourhood `{x | g * x ∉ K}`.
3. The subgroup `U = K * N` is open and proper, contains `K`, and excludes `g`:
   normality makes it a subgroup, translates of `N` make it open, and membership
   of `g` would contradict `g * N ∩ K = ∅`.
4. By `lem-dl-a1-open-subgroup-finite-cosets`, the left coset action `G/U` is finite,
   discrete and continuous. The coset `U` is `H`-fixed, giving an `H`-equivariant
   map from the terminal singleton into its restriction, with the conventions of
   `def-pod-finite-continuous-module`.
5. Fullness lifts that map to a `G`-equivariant map with the same underlying
   function. Thus every `x : G` fixes `U`, so every `x` lies in `U`, contradicting
   properness. Hence `h` is onto. Finite coset sets can be represented in any
   universe `w`, so the morphism test imposes no size restriction on `H` or `G`. -/
theorem surjective_iff_bijective_finite_res
    (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (hH : (𝓝 (1 : H)).HasBasis (fun _ : OpenNormalSubgroup H ↦ True)
      (fun N ↦ (N : Set H)))
    (hG : (𝓝 (1 : G)).HasBasis (fun _ : OpenNormalSubgroup G ↦ True)
      (fun N ↦ (N : Set G)))
    (h : H →ₜ* G) :
    Function.Surjective h ↔
      ∀ E D : ContAction FintypeCat.{w} G,
        Function.Bijective ((ContAction.res FintypeCat.{w} h).map (X := E) (Y := D)) := by
  sorry

end ContAction
