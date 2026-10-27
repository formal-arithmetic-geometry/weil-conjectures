/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact

/-! # Compact admissible balls and one-vector extension

Source: Weil blueprint, sec-six-functors-basics,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), agent scalar-extension
expansion, old steps 2--4 (blueprint: lem-sfb-ultrametric-one-vector-extension).
The explicit scalar-extension argument is absent from the blueprint itself;
the external Ingleton reference is WANTED in the DAG.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace LinearMap

/-- The admissible scalar balls are nested, have nonempty finite and total intersections,
and every scalar in their total intersection defines a bound-preserving extension to
`U ⊔ Submodule.span K {x}` by the formula `G (u + a • x) = g u + a * b`.

Source: agent scalar-extension expansion, old steps 2--4, attached to paragraph (3) of
`sk-thm-sf-ctf-stability-direct-images.proof.md`
(blueprint: lem-sfb-ultrametric-one-vector-extension).

Proof:
1. Multiplicativity gives |-1| = 1, so negation preserves the scalar and vector norms.
   The ultrametric inequalities imply the ordinary triangle inequalities. Every radius
   C ‖x-u‖ is nonnegative, and each ball contains its center g(u). Its complement is
   open: at z outside the ball, take epsilon = |z-g(u)| - C ‖x-u‖ > 0 and use the
   ordinary triangle inequality to show that this neighborhood misses the ball.
2. Linearity and the bound give |g(u)-g(v)| ≤ C ‖u-v‖ ≤ max(C ‖x-u‖, C ‖x-v‖).
   If the first radius is at most the second, the ultrametric inequality shows that
   every point of the first ball belongs to the second.
3. Among the indices in a finite set F together with zero, choose one of least radius.
   Its center belongs to B_0 and all balls indexed by F. For F empty use index zero.
4. The compact subspace B_0 has the closed family B_0 ∩ B_u. Step 3 supplies its
   finite intersection property, including the empty family. Apply
   lem-sfb-compact-closed-finite-intersection (CompactSpace.iInter_nonempty,
   Stacks Tag 005D) to obtain a scalar in every B_u.
5. Fix any such scalar b. Expressions u + a • x are unique: equality of two with
   different coefficients would put x in U, by inversion in def-weil-field.
   The formula g(u) + a*b therefore defines G. Addition and scalar multiplication
   of the coordinates prove linearity, and coefficient zero proves restriction to g.
6. For y = u + a • x, coefficient zero uses the original bound. Otherwise put
   z = -a⁻¹ • u in U. Then y = a • (x-z) and g(u) = -a*g(z), so membership in B_z
   gives |G(y)| = |a| |b-g(z)| ≤ |a| C ‖x-z‖ = C ‖y‖.
No step requires completeness, closedness of U, or a nontrivial scalar norm. -/
theorem exists_one_vector_extension_of_isCompact_closedBall
    {K : Type u} [NormedField K]
    (hK : ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    (hcompact : ∀ (c : K) (r : ℝ), 0 ≤ r → IsCompact (Metric.closedBall c r))
    {V : Type v} [NormedAddCommGroup V] [NormedSpace K V]
    (hV : ∀ y z : V, ‖y + z‖ ≤ max ‖y‖ ‖z‖)
    (U : Submodule K V) (C : ℝ) (hC : 0 < C) (g : U →ₗ[K] K)
    (hg : ∀ u : U, ‖g u‖ ≤ C * ‖(u : V)‖) (x : V) (hx : x ∉ U) :
    (∀ u : U, (Metric.closedBall (g u) (C * ‖x - (u : V)‖)).Nonempty ∧
      IsClosed (Metric.closedBall (g u) (C * ‖x - (u : V)‖))) ∧
    (∀ u w : U, C * ‖x - (u : V)‖ ≤ C * ‖x - (w : V)‖ →
      Metric.closedBall (g u) (C * ‖x - (u : V)‖) ⊆
        Metric.closedBall (g w) (C * ‖x - (w : V)‖)) ∧
    (∀ F : Finset U,
      (Metric.closedBall (g 0) (C * ‖x - ((0 : U) : V)‖) ∩
        ⋂ u ∈ F, Metric.closedBall (g u) (C * ‖x - (u : V)‖)).Nonempty) ∧
    (⋂ u : U, Metric.closedBall (g u) (C * ‖x - (u : V)‖)).Nonempty ∧
    (∀ b ∈ ⋂ u : U, Metric.closedBall (g u) (C * ‖x - (u : V)‖),
      ∃ G : ↥(U ⊔ Submodule.span K {x}) →ₗ[K] K,
        (∀ (u : U) (a : K) (y : ↥(U ⊔ Submodule.span K {x})),
          (y : V) = (u : V) + a • x → G y = g u + a * b) ∧
        G.comp (Submodule.inclusion le_sup_left) = g ∧
        ∀ y : ↥(U ⊔ Submodule.span K {x}), ‖G y‖ ≤ C * ‖(y : V)‖) := by
  sorry

end LinearMap
