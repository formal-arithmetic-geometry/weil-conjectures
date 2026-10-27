/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Locally ringed topoi and local geometric morphisms

Source: Stacks Project, Modules on Sites, Tags 04H8 and 04HA
(blueprint: def-sfb-locally-ringed-topos).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The underlying sheaf of a ring sheaf.
Source: Stacks Project, Tag 04HA (blueprint: def-sfb-locally-ringed-topos). -/
noncomputable def ringSheafUnderlying {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) : Sheaf J (Type u) :=
  (sheafCompose J (forget RingCat)).obj R

/-- The unit subsheaf, using the right adjoint `MonCat.units`.
Source: Stacks Project, Tag 04HA (blueprint: def-sfb-locally-ringed-topos). -/
noncomputable def ringSheafUnits {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) : Sheaf J (Type u) :=
  (sheafCompose J (forget₂ RingCat SemiRingCat ⋙ forget₂ SemiRingCat MonCat ⋙
    MonCat.units ⋙ forget GrpCat)).obj R

/-- Inclusion of units into the underlying ring sheaf.
Source: Stacks Project, Tag 04HA (blueprint: def-sfb-locally-ringed-topos). -/
noncomputable def ringSheafUnitsInclusion {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    ringSheafUnits R ⟶ ringSheafUnderlying R :=
  ⟨{ app := fun _ ↦ TypeCat.ofHom Units.val
     naturality := by intros; rfl }⟩

/-- Locally every section or its complement is invertible, and zero equals one only on
objects covered by the empty sieve. The latter is the intrinsic initial-equalizer condition.
Source: Stacks Project, Tags 04H8 and 04H7
(blueprint: def-sfb-locally-ringed-topos). -/
def IsLocallyRingedTopos {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) : Prop :=
  (∀ (U : C) (a : R.obj.obj (op U)),
    ∃ V : Sieve U, V ∈ J U ∧ ∀ (W : C) (f : W ⟶ U), V f →
      IsUnit (R.obj.map f.op a) ∨ IsUnit (1 - R.obj.map f.op a)) ∧
  (∀ U : C, (0 : R.obj.obj (op U)) = 1 → (⊥ : Sieve U) ∈ J U)

/-- Locality means that the structural map has a cartesian square of unit subsheaves.
The upper map is uniquely determined by the two inclusions and the structural map.
Source: Stacks Project, Tag 04HA
(blueprint: def-sfb-locally-ringed-topos). -/
def RingedToposMorphism.IsLocal
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (g : RingedToposMorphism R S) : Prop :=
  ∃ v : g.inverse.obj (ringSheafUnits S) ⟶ ringSheafUnits R,
    IsPullback v (g.inverse.map (ringSheafUnitsInclusion S))
      (ringSheafUnitsInclusion R) g.ringMap

end CategoryTheory
