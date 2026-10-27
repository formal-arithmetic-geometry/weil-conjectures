/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Category.Profinite.Basic

import Mathlib.Topology.Compactness.Compact

/-! # A contractive functional with profinite parameters

Source: the direct-images proof, paragraph (3), scalar analytic auxiliary, in
literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md.
This is an agent-formulated auxiliary assertion; an exact literature reference is WANTED.
(blueprint: lem-sfb-compact-parameter-functional)
-/

@[expose] public section

universe u v w t

namespace ContinuousMap

/-- A contractive linear functional acts on the compact variable of a continuous function.
Source: the direct-images proof, paragraph (3), scalar analytic auxiliary (agent-formulated;
exact literature reference WANTED).
(blueprint: lem-sfb-compact-parameter-functional)

The family `J` is fixed by its evaluation formula. Its values are continuous maps; the
neighbourhood estimate includes both the supremum norm of the difference of sections and
the difference of functional values. The scalar identity states linearity over `C(P, B)`
for its action on the source by multiplication with the pullback along the first projection.
The remaining identities include every finite sum and precomposition in the parameter.

Proof: (1) Each section is continuous. For fixed `p₀` and positive `ε`, the open set where
`‖f (p, x) - f (p₀, x)‖ < ε / 2` contains `{p₀} × X`.
(2) Apply `generalized_tube_lemma` (lem-sfb-compact-product-open-neighborhoods) to the
compact singleton and compact `X`; obtain an open neighbourhood `V` on which every
pointwise difference has norm less than `ε / 2`.
(3) Taking suprema gives the weak supremum bound. Linearity and contractivity give the
same bound on functional values. Since `ε / 2 < ε`, the neighbourhood criterion gives
continuity, also vacuously for empty parameters.
(4) Pointwise linearity of `L` gives additivity and linearity over parameter functions.
Induction gives the finite-sum identity, including the empty sum.
(5) The section after precomposition by `u × id` at `p'` is the original section at
`u p'`, proving naturality by extensionality, including empty source parameters.
No completeness or nonarchimedean inequality is used. -/
theorem exists_compactParameterFunctional
    (B : Type w) [NormedField B]
    (X : Type v) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    (L : C(X, B) →ₗ[B] B) (hL : ∀ g : C(X, B), ‖L g‖ ≤ ‖g‖) :
    ∃ J : ∀ P : Profinite.{u}, C(P × X, B) →ₗ[B] C(P, B),
      (∀ (P : Profinite.{u}) (f : C(P × X, B)) (p : P),
        J P f p = L (f.curry p)) ∧
      (∀ (P : Profinite.{u}) (f : C(P × X, B)) (p₀ : P) (ε : ℝ), 0 < ε →
        ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ ∀ p ∈ V,
          ‖f.curry p - f.curry p₀‖ ≤ ε / 2 ∧
          ‖J P f p - J P f p₀‖ ≤ ε / 2) ∧
      (∀ (P : Profinite.{u}) (c : C(P, B)) (f : C(P × X, B)),
        J P (c.comp ContinuousMap.fst * f) = c * J P f) ∧
      (∀ (P : Profinite.{u}) (T : Type t) [Fintype T] (f : T → C(P × X, B)),
        J P (∑ i, f i) = ∑ i, J P (f i)) ∧
      (∀ (P P' : Profinite.{u}) (a : C(P', P)) (f : C(P × X, B)),
        J P' (f.comp (a.prodMap (ContinuousMap.id X))) = (J P f).comp a) := by
  sorry

end ContinuousMap
