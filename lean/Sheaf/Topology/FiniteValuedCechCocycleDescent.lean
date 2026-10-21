/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.AlgebraicTopology.SetCechNerveFreeResolution
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Profinite
import Sheaf.Topology.FiniteQuotientFiberProduct

/-!
# Descent of finite-valued continuous Cech cocycles

Source: Stacks Project, Topology, Tags 08ZY, 08ZZ and 0A2P, applied to finite quotient
surjections; the explicit finite-coefficient reduction for Bhatt--Scholze,
The pro-etale topology for schemes, Lemma 4.3.9(2), printed p. 33
(blueprint: lem-sfb-finite-valued-cech-cocycle-descent).

The fibre powers and coordinate deletions use the existing set Cech nerve. Its subtype
inherits the finite-product topology. The descended equation holds on all quotient tuples.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators
open AlgebraicTopology

namespace AlgebraicTopology

/-- The subtype topology on the existing set Cech nerve inside the finite product.
Source: Stacks Project, Topology, Tag 08ZY, fibre powers with their subspace topology
(blueprint: lem-sfb-finite-valued-cech-cocycle-descent). -/
instance setCechNerveTopologicalSpace {A B : Type u} [TopologicalSpace A]
    (f : A → B) (n : ℕ) : TopologicalSpace (setCechNerve f n) :=
  TopologicalSpace.induced (fun x : setCechNerve f n ↦ x.val) inferInstance

end AlgebraicTopology

namespace Topology

/-- A continuous finite-valued positive-degree Cech cocycle descends, with its equation,
to a finite discrete quotient surjection.

Source: Stacks Project, Topology, Tags 08ZY (lemma-profinite),
08ZZ (lemma-profinite-refine-open-covering), and 0A2P (lemma-describe-limits),
applied to compatible finite quotient diagrams; agent-formulated discrete-coefficient
input to Bhatt--Scholze, Lemma 4.3.9(2)
(blueprint: lem-sfb-finite-valued-cech-cocycle-descent).

Proof: (1) If S is empty, so is T; use empty finite quotients. Otherwise iterate
lem-sfb-finite-quotient-fiber-product to obtain compact Hausdorff totally disconnected
finite products and fibre powers. (2) Continuity into the discrete group, the clopen
basis lem-weil-pbc-profinite-clopen-basis, and compactness give finitely many clopen
rectangles covering the fibre power, on each of which c is constant.
(3) Take the atoms of all coordinate clopens. On each product cell meeting the fibre
power extend c by its constant value, and use zero on the other cells. This defines a
continuous function h on the whole product. (4) Its alternating sum e on the next
product is continuous and vanishes on the next fibre power. Its nonzero locus D is
clopen and compact. (5) For each tuple in D some two base images differ. Separate them
by a clopen in S using lem-weil-pbc-profinite-clopen-basis. Compactness selects finitely
many such separations. Let gamma be their atom partition: e vanishes on every tuple
whose base images lie in a single gamma block. (6) Refine the coordinate atom partition
by inverse images of gamma. Its nonempty blocks form T₀, the gamma blocks form S₀,
and the block projections a and b are continuous and surjective. Send a T₀ block to
its gamma block to obtain the surjection q₀ and q₀ a = b q.
(7) Since h is constant on products of T₀ blocks, it descends to h₀; restrict h₀ to the
quotient fibre power to obtain c₀. Its pullback is c. (8) For any quotient tuple choose
representatives independently. Their base images lie in the same gamma block, so the
alternating sum of h at these representatives is zero by step 5, which is precisely
the equation for c₀. Equal base images of representatives are unnecessary, so the
argument includes nonliftable quotient tuples. For the zero group h = e = 0 and the
same construction works. -/
theorem finite_valued_cech_cocycle_descent
    (T S : Type u) [TopologicalSpace T] [TopologicalSpace S]
    [CompactSpace T] [CompactSpace S] [T2Space T] [T2Space S]
    [TotallyDisconnectedSpace T] [TotallyDisconnectedSpace S]
    (q : C(T, S)) (hq : Function.Surjective q)
    (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (n : ℕ) (hn : 1 ≤ n) (c : C(setCechNerve q n, M))
    (hc : ∀ x : setCechNerve q (n + 1),
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • c (setCechFace q j x) = 0) :
    ∃ (T₀ S₀ : Type u) (_ : Finite T₀) (_ : Finite S₀)
      (_ : TopologicalSpace T₀) (_ : TopologicalSpace S₀)
      (_ : DiscreteTopology T₀) (_ : DiscreteTopology S₀)
      (a : C(T, T₀)) (b : C(S, S₀)) (q₀ : T₀ → S₀),
      Function.Surjective a ∧ Function.Surjective b ∧ Function.Surjective q₀ ∧
      ∃ (hcomm : ∀ t : T, q₀ (a t) = b (q t)) (c₀ : setCechNerve q₀ n → M),
        (∀ x : setCechNerve q n,
          c x = c₀ ⟨fun i ↦ a (x.val i), fun i ↦
            (hcomm (x.val i)).trans
              ((congrArg b (x.property i)).trans (hcomm (x.val 0)).symm)⟩) ∧
        (∀ x : setCechNerve q₀ (n + 1),
          ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • c₀ (setCechFace q₀ j x) = 0) := by
  sorry

end Topology
