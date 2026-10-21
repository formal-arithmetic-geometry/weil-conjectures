/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.CategoryTheory.Action.Continuous
public import Sheaf.Topology.ProfiniteCondensedRing

/-! # Trivial and free profinite action parameters

Source: main-20261015, direct-image stability, paragraph (3), the agent-formulated
finite-cover action-space infrastructure, trivial parameters and free evaluation
(blueprint: def-sfb-profinite-action-parameters).

These functors give the trivial action on a parameter and left translation on the
first factor of its product with the group. They have no field or Galois input.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace Profinite.ContinuousActionParameter

/-- Equip a profinite parameter with the trivial continuous action, retaining every map.
Source: paragraph (3), the trivial-parameter functor t
(blueprint: def-sfb-profinite-action-parameters). -/
def trivialAction (G : Type u) [Group G] [TopologicalSpace G] :
    Profinite.{u} ⥤ ContAction Profinite.{u} G where
  obj P := ⟨Action.trivial G P, ⟨continuous_snd⟩⟩
  map f := ObjectProperty.homMk
    { hom := f
      comm := fun _ ↦ by simp [Action.trivial] }

/-- Form the product with the group, with left translation on its first factor;
a parameter map is sent to its product with the identity of the group.
Source: paragraph (3), the free-parameter functor H in proof steps 6--10
(blueprint: def-sfb-profinite-action-parameters). -/
def freeAction (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    Profinite.{u} ⥤ ContAction Profinite.{u} G where
  obj P :=
    ⟨{ V := Profinite.of (G × P)
       ρ :=
        { toFun := fun g ↦ CompHausLike.ofHom _
            ⟨fun x ↦ (g * x.1, x.2), by fun_prop⟩
          map_one' := by
            apply ConcreteCategory.hom_ext
            intro x
            exact Prod.ext (one_mul x.1) rfl
          map_mul' := by
            intro g h
            apply ConcreteCategory.hom_ext
            intro x
            exact Prod.ext (mul_assoc g h x.1) rfl } },
     ⟨by
       change Continuous (fun x : G × (G × P) ↦ (x.1 * x.2.1, x.2.2))
       fun_prop⟩⟩
  map f := ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨fun x ↦ (x.1, f x.2), by fun_prop⟩
      comm := fun _ ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        rfl }
  map_id P := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  map_comp {P Q R} f g := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro x
    rfl

end Profinite.ContinuousActionParameter
