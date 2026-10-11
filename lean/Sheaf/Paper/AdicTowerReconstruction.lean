/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Reconstruction from an adic tower

Source: Stacks Project, Algebra, Lemma 09B8 (lemma-limit-complete)
(blueprint: lem-pod-adic-tower-reconstruction).
-/

@[expose] public section

universe u v w

namespace Ideal

/-- Source: Stacks Project, Algebra, Lemma 09B8 (lemma-limit-complete)
(blueprint: lem-pod-adic-tower-reconstruction).
Here `N n` denotes the paper's `M_{n+1}`. A module over `A / I^(n+1)` is expressed as
an `A`-module annihilated by `I^(n+1)`. The surjectivity and kernel conditions on `t`
say precisely that its induced quotient map is an isomorphism. The maps `p` present
`L` as the inverse limit: every compatible family is the image of exactly one element.
The infimum of the topologies induced by `p n` from the discrete topology is the
inverse-limit topology.

Proof: (1) Surjective transitions allow recursive lifts, so each projection is surjective;
it kills `I^(n+1) L`. (2) The canonical map from `L` to its completion has a left inverse
obtained from these projections. Completion along a finitely generated ideal is complete
(lem-weil-pbc-module-completion-complete, Stacks 05GG), and completeness passes to this
retract, as in Stacks 09B7. (3) Put `K n = ker (p n)`. The quotient transition hypothesis
makes the transitions on `K n / (K n ∩ I^(n+1) L)` surjective. Their inverse limit is the
kernel of the map from the completion to `L`, hence zero by (2). Surjectivity then forces
every term to vanish, so `K n = I^(n+1) L`. (4) Thus the induced quotient maps are
isomorphisms, and intersection of the kernels is zero. (5) These same kernels are the
basic zero neighborhoods of the inverse-limit topology and of the adic topology. -/
theorem adic_tower_reconstruction
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (N : ℕ → Type v) [∀ n, AddCommGroup (N n)] [∀ n, Module A (N n)]
    (t : ∀ n, N (n + 1) →ₗ[A] N n)
    (hN : ∀ n, (I ^ (n + 1) • ⊤ : Submodule A (N n)) = ⊥)
    (ht : ∀ n, Function.Surjective (t n) ∧
      (t n).ker = (I ^ (n + 1) • ⊤ : Submodule A (N (n + 1))))
    (L : Type w) [AddCommGroup L] [Module A L]
    (p : ∀ n, L →ₗ[A] N n)
    (hp : ∀ n, (t n).comp (p (n + 1)) = p n)
    (hlim : ∀ x : ∀ n, N n, (∀ n, t n (x (n + 1)) = x n) →
      ∃! y : L, ∀ n, p n y = x n) :
    (∀ n, ∃ e : (L ⧸ (I ^ (n + 1) • ⊤ : Submodule A L)) ≃ₗ[A] N n,
      ∀ y : L, e ((I ^ (n + 1) • ⊤ : Submodule A L).mkQ y) = p n y) ∧
    IsAdicComplete I L ∧ IsHausdorff I L ∧
    (⨅ n, TopologicalSpace.induced (p n) (⊥ : TopologicalSpace (N n))) =
      I.adicModuleTopology L := by
  sorry

end Ideal
