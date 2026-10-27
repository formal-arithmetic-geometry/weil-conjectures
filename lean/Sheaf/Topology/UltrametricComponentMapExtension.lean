/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.ContinuousMap.Algebra

import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Continuous ultrametric functions across a component homeomorphism

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 4.2.12,
last proof paragraph; the arbitrary-space and ring-isomorphism argument of the DAG node
(blueprint: lem-sfb-ultrametric-component-map-extension).

The multiplicative absolute value and its induced metric are encoded by `NormedField`.
The displayed nonarchimedean inequality allows the trivial absolute value.
`ConnectedComponents` carries the quotient topology, and `C(T, A)` has pointwise operations.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace ContinuousMap

/-- Continuous functions into a nonarchimedean normed field factor uniquely through
connected components. Actual precomposition with a map inducing a component homeomorphism
is a ring isomorphism, whose inverse composes that unique factor with the inverse
homeomorphism and the quotient map.

Source: Bhatt--Scholze, Lemma 4.2.12, last proof paragraph, generalized to arbitrary spaces
by the elementary argument in the node
(blueprint: lem-sfb-ultrametric-component-map-extension).

Proof for stage 3:
1. From a-c = (a-b) + (b-c), the nonarchimedean inequality gives the ultrametric
   inequality for the genuine norm metric. Apply
   lem-sfb-ultrametric-space-totally-disconnected (Mathlib's ultrametric total-separation
   instance and `TotallySeparatedSpace.totallyDisconnectedSpace`). No completeness or
   nontriviality of the absolute value is required.
2. Apply lem-sfb-continuous-connected-component-lift to Y and Z, with target A.
   `Continuous.connectedComponentsLift` constructs each factor; its continuity,
   composite and uniqueness theorems give the two unique continuous factorizations.
   `ConnectedComponents.continuous_coe` and `ConnectedComponents.surjective_coe` supply
   continuity and surjectivity of the quotient maps.
3. Pointwise operations make the continuous maps a ring: constants are continuous,
   negation is an isometry, and addition satisfies the given maximum bound on differences.
   For multiplication near (x,y), put M = 1 + |x| + |y| and choose positive delta less
   than both 1 and epsilon/M. Input differences less than delta give |x'| at most M
   and |x'y'-xy| at most max(|x'| |y'-y|, |y| |x'-x|), less than epsilon.
   Actual precomposition preserves every pointwise ring operation; it is precisely
   `(ContinuousMap.compRightAlgHom A A i).toRingHom`.
4. For f on Y define E(f) by composing its unique factor with h inverse and q_Z.
   The normalization of h gives i*(E(f)) = f. If g is on Z, its component factor
   composed with h factors g composed with i; uniqueness identifies this with the
   component factor of i*(g), giving E(i*(g)) = g. Thus precomposition is a bijective
   ring homomorphism. Its inverse preserves ring operations by applying the injective
   forward ring homomorphism to each equality. This also proves the displayed inverse
   formula for every factor satisfying the factorization equation.
   If Y is empty, the component homeomorphism forces Z empty; both function rings
   are singleton rings. A trivial absolute value gives a discrete genuine metric,
   so the same proof applies. -/
theorem ultrametric_component_map_extension
    {Y : Type u} {Z : Type v} {A : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z] [NormedField A]
    (i : C(Y, Z)) (h : ConnectedComponents Y ≃ₜ ConnectedComponents Z)
    (hcomm : ∀ y : Y, h (ConnectedComponents.mk y) = ConnectedComponents.mk (i y))
    (hna : ∀ a b : A, ‖a + b‖ ≤ max ‖a‖ ‖b‖) :
    TotallyDisconnectedSpace A ∧
    (∀ f : C(Y, A), ∃! fbar : C(ConnectedComponents Y, A),
      f = fbar.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) ∧
    (∀ g : C(Z, A), ∃! gbar : C(ConnectedComponents Z, A),
      g = gbar.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) ∧
    ∃ e : C(Z, A) ≃+* C(Y, A),
      e.toRingHom = (ContinuousMap.compRightAlgHom A A i).toRingHom ∧
      ∀ (f : C(Y, A)) (fbar : C(ConnectedComponents Y, A)),
        f = fbar.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ →
        e.symm f = (fbar.comp ⟨h.symm, h.symm.continuous⟩).comp
          ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ := by
  classical
  have : IsUltrametricDist A := ⟨fun a b c ↦ by
    simpa only [dist_eq_norm, sub_add_sub_cancel] using hna (a - b) (b - c)⟩
  have : TotallyDisconnectedSpace A := inferInstance
  have factorY (f : C(Y, A)) : ∃! fbar : C(ConnectedComponents Y, A),
      f = fbar.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ := by
    refine ⟨⟨f.continuous.connectedComponentsLift,
      f.continuous.connectedComponentsLift_continuous⟩, ?_, ?_⟩
    · ext y
      rfl
    · intro fbar hfbar
      apply ContinuousMap.coe_injective
      exact f.continuous.connectedComponentsLift_unique fbar
        (congrArg DFunLike.coe hfbar.symm)
  have factorZ (g : C(Z, A)) : ∃! gbar : C(ConnectedComponents Z, A),
      g = gbar.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ := by
    refine ⟨⟨g.continuous.connectedComponentsLift,
      g.continuous.connectedComponentsLift_continuous⟩, ?_, ?_⟩
    · ext z
      rfl
    · intro gbar hgbar
      apply ContinuousMap.coe_injective
      exact g.continuous.connectedComponentsLift_unique gbar
        (congrArg DFunLike.coe hgbar.symm)
  refine ⟨inferInstance, factorY, factorZ, ?_⟩
  let F : C(Z, A) →+* C(Y, A) := (ContinuousMap.compRightAlgHom A A i).toRingHom
  let E (f : C(Y, A)) : C(Z, A) :=
    ⟨fun z ↦ f.continuous.connectedComponentsLift (h.symm (ConnectedComponents.mk z)),
      f.continuous.connectedComponentsLift_continuous.comp
        (h.symm.continuous.comp ConnectedComponents.continuous_coe)⟩
  have lift_comp (g : C(Z, A)) (c : ConnectedComponents Y) :
      (g.comp i).continuous.connectedComponentsLift c =
        g.continuous.connectedComponentsLift (h c) := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [hcomm]
    rfl
  have right_inv (f : C(Y, A)) : F (E f) = f := by
    ext y
    change f.continuous.connectedComponentsLift (h.symm (ConnectedComponents.mk (i y))) = f y
    rw [← hcomm, h.symm_apply_apply]
    rfl
  have left_inv (g : C(Z, A)) : E (F g) = g := by
    ext z
    change (g.comp i).continuous.connectedComponentsLift
      (h.symm (ConnectedComponents.mk z)) = g z
    rw [lift_comp, h.apply_symm_apply]
    rfl
  let e : C(Z, A) ≃+* C(Y, A) := RingEquiv.ofBijective F
    ⟨Function.HasLeftInverse.injective ⟨E, left_inv⟩,
      Function.HasRightInverse.surjective ⟨E, right_inv⟩⟩
  refine ⟨e, rfl, ?_⟩
  intro f fbar hfbar
  apply e.injective
  rw [e.apply_symm_apply]
  change f = F ((fbar.comp ⟨h.symm, h.symm.continuous⟩).comp
    ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩)
  ext y
  change f y = fbar (h.symm (ConnectedComponents.mk (i y)))
  rw [← hcomm, h.symm_apply_apply]
  exact congrArg (fun g : C(Y, A) ↦ g y) hfbar

end ContinuousMap
