/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat
import Sheaf.RepresentationTheory.DiscreteContinuousRep
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Finite modules with continuous linear group actions

Source: Stacks Project, Tag 0DV5, proof of (3)
(blueprint: def-pod-finite-continuous-module).
-/

section

universe r g u

open CategoryTheory

open scoped FintypeCatDiscrete

namespace CategoryTheory

/-- Finite linear representations with continuous action on the discrete carrier.
Source: Stacks Tag 0DV5, proof of (3) (blueprint: def-pod-finite-continuous-module).
`Rep.DiscreteContinuousRep R G` has equivariant linear maps as morphisms. For a group, its
endomorphisms are automatically automorphisms. Open stabilizers are equivalent to joint
continuity since the module has the discrete topology. -/
def FiniteContinuousModule (R : Type r) [Ring R] (G : Type g) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :=
  ObjectProperty.FullSubcategory
    (fun A : Rep.DiscreteContinuousRep.{r, g, u} R G ↦ Finite A.obj.V)

/-- The category structure is inherited from the full subcategory of linear actions.
Source: Stacks Tag 0DV5 (blueprint: def-pod-finite-continuous-module). -/
instance finiteContinuousModuleCategory (R : Type r) [Ring R] (G : Type g) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : Category (FiniteContinuousModule.{r, g, u} R G) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory _))

/-- Forget finiteness, continuity, and module structure, retaining the group action.
Source: Stacks Tag 0DV5 (blueprint: def-pod-finite-continuous-module). -/
def FiniteContinuousModule.forget (R : Type r) [Ring R] (G : Type g) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    FiniteContinuousModule.{r, g, u} R G ⥤ Action (Type u) G :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction R G ⋙
    (CategoryTheory.forget (ModuleCat R)).mapAction G

/-- Finite continuous group sets have finite products and a terminal object.
Source: Stacks Tag 0DV5 (blueprint: def-pod-finite-continuous-module).
Proof: use the Cartesian product with the diagonal action and the singleton with
trivial action. Products are finite and the coordinate actions are continuous;
the pairing of equivariant maps is equivariant. -/
theorem finiteContAction_hasFiniteProducts (G : Type g) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Limits.HasFiniteProducts (ContAction FintypeCat.{u} G) := by
  sorry

/-- Choose finite products for finite continuous group sets.
Source: Stacks Tag 0DV5 (blueprint: def-pod-finite-continuous-module). -/
noncomputable instance finiteContActionFiniteProducts (G : Type g) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    Limits.HasFiniteProducts (ContAction FintypeCat.{u} G) :=
  finiteContAction_hasFiniteProducts G

/-- Forget continuity and finiteness of a finite continuous group set.
Source: Stacks Tag 0DV5 (blueprint: def-pod-finite-continuous-module). -/
def finiteContActionForget (G : Type g) [Group G] [TopologicalSpace G] :
    ContAction FintypeCat.{u} G ⥤ Action (Type u) G :=
  ObjectProperty.ι _ ⋙ (CategoryTheory.forget FintypeCat).mapAction G

end CategoryTheory

end
