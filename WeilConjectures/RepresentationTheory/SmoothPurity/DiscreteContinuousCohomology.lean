/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.Continuous.ContinuousCochainsDerivedInvariants

/-!
# Continuous cohomology of discrete profinite modules

We define the cohomology functors `H^q(G, -)` on discrete `A`-modules with a continuous action
of a profinite group `G`, as right derived functors of invariants.

## Implementation details

The abelian structure on `DiscreteContinuousRep A G` and the invariant functor are chosen from
the existence statements `discreteModules_abelian` and `continuousCochains_derived_invariants`.
The latter also identifies the derived functors with the cohomology of the continuous
inhomogeneous cochain complex. No finiteness condition is imposed on the modules.

## References

* Stacks Project, Tags 04JP, 04JR and 0DVG.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

/-- The functor `H^q(G, -)` on discrete left `A`-modules with continuous `G`-action.
Its value on `M` is the `q`-th right derived functor of the invariants functor
`M ↦ {m | ∀ g, ρ g m = m}` on the abelian category `DiscreteContinuousRep A G`. -/
noncomputable def discreteContinuousCohomologyFunctor
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] (q : ℕ) :
    DiscreteContinuousRep.{v, u, max u w} A G ⥤ ModuleCat.{max u w} A :=
  let h := Classical.choose (discreteModules_abelian.{u, v, max u w} G A)
  letI := h
  letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := h.toPreadditive
  letI : Preadditive (ModuleCat.{max u w} A) :=
    (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
  letI := (Classical.choose_spec
    (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.1
  letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, TopologicalSpace M.obj.V :=
    fun _ ↦ ⊥
  letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, DiscreteTopology M.obj.V :=
    fun _ ↦ ⟨rfl⟩
  letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
      ContinuousConstSMul A M.obj.V :=
    fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
  let comparison := continuousCochains_derived_invariants.{u, v, w} G A
  let V := Classical.choose comparison
  let a := Classical.choose (Classical.choose_spec comparison)
  @Functor.rightDerived _ _ _ _ h _ _ V a q

end Rep
