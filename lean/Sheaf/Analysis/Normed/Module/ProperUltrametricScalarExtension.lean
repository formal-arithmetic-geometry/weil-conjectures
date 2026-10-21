/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn

/-! # Scalar extension over a proper ultrametric field

Source: Weil blueprint, main-20261015, sec-six-functors-basics,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), arithmetic
coefficient-topology expansion (blueprint: lem-sfb-proper-ultrametric-scalar-extension).

This is the scalar-valued nonarchimedean Hahn–Banach extension statement.
The supplied DAG gives an agent-written proof using compact scalar balls and Zorn;
the argument is absent from the blueprint itself. The Ingleton reference is WANTED.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ContinuousLinearMap

/-- A continuous scalar-valued linear map on any subspace of an ultrametric normed
space extends continuously to the whole space when the scalar field has compact
closed balls and an element of norm strictly between zero and one.

Source: Weil blueprint, main-20261015, sec-six-functors-basics,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), arithmetic
coefficient-topology expansion (blueprint: lem-sfb-proper-ultrametric-scalar-extension).
The scalar-extension proof below is agent-written, not present in the blueprint;
A. W. Ingleton, The Hahn-Banach theorem for non-Archimedean valued fields, is WANTED.

Proof:
1. The ultrametric inequalities imply the ordinary triangle inequalities. The
   element of norm between zero and one makes the scalar norm nontrivial. Apply
   lem-trf-continuous-linear-map-norm-bound (ContinuousLinearMap.bound) to obtain
   a fixed C > 0 with |f(w)| ≤ C ‖w‖.
2. For any bounded partial extension g on U containing W and x outside U, consider
   B_u = {b : K | |b - g(u)| ≤ C ‖x - u‖}. The ultrametric inequalities and the bound
   on g show that the distance between two centers is at most the larger radius.
   Therefore these nonempty closed balls are totally ordered by inclusion.
3. Inside the compact ball B_0, every finite intersection of the B_u contains the
   center of a ball of least radius among those indexed by the finite set and zero.
   This includes the empty finite set. By lem-sfb-compact-closed-finite-intersection
   (CompactSpace.iInter_nonempty), choose b in every B_u.
4. Uniqueness of the expression u + a x defines G(u + a x) = g(u) + a b on U + Kx.
   It is linear and extends g. For a ≠ 0, put z = -a⁻¹ u. Membership b ∈ B_z and
   homogeneity give |G(u + a x)| = |a| |b - g(z)| ≤ C ‖u + a x‖. The a = 0 case
   follows from the bound on g.
5. Order the graphs of bounded partial extensions by inclusion. A nonempty chain
   has its union as an upper bound: any two domain elements lie in a common member,
   so its value is well-defined and linear, with the same bound. The graph of f is
   an upper bound for the empty chain.
6. Apply lem-weil-pbc-zorn-lemma (zorn_subset). If the domain of a maximal graph
   were proper, steps 2–4 would give a strictly larger bounded extension. Hence its
   domain is all of V.
7. The resulting map restricts to f and satisfies |g(v) - g(w)| ≤ C ‖v - w‖.
   Taking delta = epsilon / C proves continuity for the given norm metrics.
-/
theorem exists_extension_of_proper_ultrametric
    {K : Type u} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    (hnontrivial : ∃ t : K, 0 < ‖t‖ ∧ ‖t‖ < 1)
    {V : Type v} [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]
    (W : Submodule K V) (f : W →L[K] K) :
    ∃ g : V →L[K] K, ∀ w : W, g (w : V) = f w := by
  sorry

end ContinuousLinearMap
