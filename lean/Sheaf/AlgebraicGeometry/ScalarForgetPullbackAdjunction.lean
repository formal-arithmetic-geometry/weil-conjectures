/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization

/-! # Canonical scalar-forgetful inverse-image comparison with adjunction and unit coherence

Source: Stacks Project, Tags 0096 and 01F7.
(blueprint: new-sc-scalar-forget-pullback-adjunction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme
open Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory

/-- Canonical scalar-forgetful inverse-image comparison with adjunction and unit coherence.
Source: Stacks Project, Tags 0096 and 01F7.
(blueprint: new-sc-scalar-forget-pullback-adjunction).

Proof: Adjunct the forgotten scalar inverse-image unit to obtain a natural map
from abelian inverse image to forgotten scalar inverse image. On every stalk this
is the map identifying the same filtered colimit of underlying abelian groups,
since forgetting a field action preserves filtered colimits. It is therefore an
isomorphism; invert it to obtain c. Naturality and the adjunction triangle identity
give the first equation for every q. For the integer-unit equation, pass through
the constant-integer sections adjunction: both maps carry the integer generator
to the scalar section 1. The constant-sheaf pullback comparison carries this same
section to 1, and the definition of scalarInverseUnitIso is its scalar analogue.
Equality on the generator proves equality of the sheaf maps. This proof works
for zero sheaves, the empty scheme, and fields of every characteristic. -/
theorem scalar_forget_pullback_adjunction (k : Type u) [Field k]
    {X Y : Scheme.{u}} (a : Y ⟶ X) :
    let L := (Opens.map a.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    ∃ c : scalarInverseImage (k := k) a ⋙ scalarAbelianForget k Y ≅
        scalarAbelianForget k X ⋙ L,
      (∀ (F : KSheaf X k) (G : KSheaf Y k)
        (q : (scalarInverseImage a).obj F ⟶ G),
        (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).homEquiv
          _ _) (c.inv.app F ≫ (scalarAbelianForget k Y).map q) =
        (scalarAbelianForget k X).map
          ((((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k) _ _).homEquiv
            _ _) q)) ∧
      Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k Y) ≫
          (scalarAbelianForget k Y).map (scalarInverseUnitIso a).inv ≫
          c.hom.app (𝟙_ (KSheaf X k)) =
        (((Opens.map a.base).constantSheafsheafPullbackIso AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
          isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ))).hom ≫
        L.map (Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k X)) := by sorry

end AlgebraicGeometry.Scheme
