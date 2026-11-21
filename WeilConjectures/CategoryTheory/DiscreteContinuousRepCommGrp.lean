/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrpAux

/-!
# Commutative group objects in discrete continuous actions

Source: Stacks Project, Tag 04JQ.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace Rep

attribute [local instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

/-- Commutative group objects in discrete continuous `G`-sets are equivalent to discrete
continuous integer representations of `G`, compatibly with the forgetful functors to
`G`-sets.
Source: Stacks Project, Tag 04JQ. -/
theorem discreteContinuousRep_commGrp
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    let D := DiscreteContinuousRep.{0, u, w} ℤ G
    let U : D ⥤ Rep.{w} ℤ G := ObjectProperty.ι _
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
    ∃ E : CommGrp (DiscreteContAction (Type w) G) ≌ D,
      Nonempty (E.functor ⋙ U ⋙ RepToAction ℤ G ⋙
        (CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G ≅
          CommGrp.forget _ ⋙ V) := by
  dsimp
  obtain ⟨E, ⟨e, he⟩⟩ :=
    discreteContinuousRep_equiv_with_compatible_objectwise_iso G
  refine ⟨E, ⟨NatIso.ofComponents e he⟩⟩

end Rep
