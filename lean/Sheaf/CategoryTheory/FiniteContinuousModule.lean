/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Finite modules with continuous linear group actions

Source: Stacks Project, Tag 0DV5, proof of (3)
(blueprint: def-pod-finite-continuous-module).
-/

@[expose] public section

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
  classical
  open Limits in
    refine ⟨fun n ↦ ⟨fun F ↦ ?_⟩⟩
    let X (i : Fin n) := (F.obj ⟨i⟩).obj.V
    let A : Action FintypeCat.{u} G :=
      { V := FintypeCat.of (∀ i, X i)
        ρ :=
          { toFun := fun g ↦ FintypeCat.homMk
              (fun x i ↦ ConcreteCategory.hom ((F.obj ⟨i⟩).obj.ρ g) (x i))
            map_one' := by
              apply ConcreteCategory.hom_ext
              intro x
              funext i
              exact ConcreteCategory.congr_hom ((F.obj ⟨i⟩).obj.ρ.map_one) (x i)
            map_mul' := by
              intro g h
              apply ConcreteCategory.hom_ext
              intro x
              funext i
              exact ConcreteCategory.congr_hom ((F.obj ⟨i⟩).obj.ρ.map_mul g h) (x i) } }
    have hA : A.IsContinuous := by
      rw [Action.isContinuous_def]
      let : TopologicalSpace (∀ i, X i) := ⊥
      have : DiscreteTopology (∀ i, X i) := ⟨rfl⟩
      change Continuous (fun p : G × (∀ i, X i) ↦
        fun i ↦ ConcreteCategory.hom ((F.obj ⟨i⟩).obj.ρ p.1) (p.2 i))
      apply continuous_prod_of_discrete_right.mpr
      intro x
      change @Continuous G (∀ i, X i) _ ⊥ _
      rw [← (show (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) = ⊥ from
        DiscreteTopology.eq_bot)]
      apply continuous_pi
      intro i
      exact (F.obj ⟨i⟩).property.continuous_smul.comp
        (continuous_id.prodMk continuous_const)
    let P : ContAction FintypeCat.{u} G := ⟨A, hA⟩
    let c : Cone F :=
      { pt := P
        π := Discrete.natTrans (fun i ↦ ObjectProperty.homMk
          { hom := FintypeCat.homMk (fun x ↦ x i.as)
            comm := fun _ ↦ rfl }) }
    refine ⟨⟨c, ?_⟩⟩
    refine
      { lift := fun s ↦ ObjectProperty.homMk
          { hom := FintypeCat.homMk (fun x i ↦ (s.π.app ⟨i⟩).hom.hom x)
            comm := fun g ↦ by
              apply ConcreteCategory.hom_ext
              intro x
              funext i
              exact ConcreteCategory.congr_hom ((s.π.app ⟨i⟩).hom.comm g) x }
        fac := fun s i ↦ by rfl
        uniq := fun s m hm ↦ ?_ }
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    ext x i
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.hom) (hm ⟨i⟩)) x

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
