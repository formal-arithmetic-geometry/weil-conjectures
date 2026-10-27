/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Topology.ProfiniteIntegralScalarDefinitions

/-! # Morphism families from the universal section

Source: HRS Example 3.1 and Remark 3.2, with the argument in
`lem-sfb-profinite-integral-scalar-realization`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj

namespace Profinite.IntegralScalar

/-- Evaluate a module morphism on the universal section over P × B. This determines
its unique continuous fibrewise linear family, before any finite reduction is taken.

Source: HRS Example 3.1; step 7 of
`lem-sfb-profinite-integral-scalar-realization`.
(blueprint: lem-sfb-profinite-universal-section-morphism)

Proof: Since B is profinite, P × B → P is an object of the slice. Apply v to its
universal B-valued section, the second projection, and use d.sections to obtain g.
For any section b over Q, the graph q ↦ (Q.hom q,b(q)) is a map over P. Naturality of
v and the restriction equations for c and d give the required morphism formula.
On the one-point object over p, the sectionwise additive map is O-linear: its action
compatibility, evaluated on the tensor of a constant scalar and any section, becomes
ordinary scalar compatibility by c.action and d.action. Its values agree with g(p,-)
by the same graph formula. This gives the linear map in Represents at each p.
Finally applying any representing formula to the universal section recovers g itself,
so all representing continuous families equal g. Conversely g represents v by the
previous calculations. For empty P the universal object is empty and uniqueness is
extensional; the zero module also has its usual universal section.
-/
theorem universal_section_morphism (P : Profinite.{u}) (O B D : Type u) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O]
    [AddCommGroup B] [Module O B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [ContinuousSMul O B] [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B]
    [AddCommGroup D] [Module O D] [TopologicalSpace D] [IsTopologicalAddGroup D]
    [ContinuousSMul O D]
    (M N : Mod (Sheaf (topology P) Ab.{u + 1}) (ring P O))
    (c : ContinuousCoordinates P O B M) (d : ContinuousCoordinates P O D N) (v : M ⟶ N) :
    ∃ g : C(P × B, D),
      ∀ g' : C(P × B, D), Represents P O B D c d v g' ↔ g' = g := by sorry

end Profinite.IntegralScalar
