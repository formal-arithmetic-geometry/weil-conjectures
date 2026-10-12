/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Topology.PresheafModuleStalkFunctor
public import Sheaf.Topology.InverseImageModule
import Sheaf.Topology.InverseImageStalk

/-!
# Natural semilinear inverse-image stalk comparison

Source: Stacks Project, Sheaves, Tags 008H and 0098.
(blueprint: lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Natural semilinear comparison for the explicitly constructed inverse image.
Source: Stacks Project, Sheaves, Tag 0098, proof using Tag 008H.

Proof: identify the chosen sheaf pullback with presheaf pullback followed by
sheafification using uniqueness of left adjoints. Apply the ring and abelian
stalk comparisons of Tag 008H, transporting them through this identification.
The ring map is stalkPullbackHom followed by stalk of toSheafify; both are
isomorphisms. The analogous abelian map defines c. To verify
semilinearity, represent the scalar and vector on neighborhoods of f(x), restrict
both to their intersection, and apply the germ formulas for the two comparisons.
The semilinearity clause of exists_inverseImageModuleInstances identifies the
unit of r times m with the product of the two units. The stalk germ scalar law
then gives the asserted equation. For naturality, represent m by a germ, use
naturality of the abelian inverse-image unit, and use stalkFunctor_map_germ_apply.
The map on the right is exactly stalkAddMap of inverseImageModuleMap by definition.
The construction applies to zero modules and zero rings; with empty X there is
no x. No flatness or nonvanishing hypothesis is used.
(blueprint: lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality). -/
theorem exists_inverseImage_stalk_comparison_natural
    (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier) (x : X) :
    let k : Y.presheaf.stalk (f x) ⟶
        TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.carrier)
          (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj x :=
      TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf))
    ∃ (c : ∀ M : RingedSpace.Modules Y,
      (RingedSpace.moduleStalkFunctor Y (f x)).obj M ≃+
        TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)
          (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val.presheaf x),
      (∀ (M : RingedSpace.Modules Y) (r : Y.presheaf.stalk (f x))
        (m : (RingedSpace.moduleStalkFunctor Y (f x)).obj M),
        c M (r • m) = k.hom r • c M m) ∧
      ∀ (M N : RingedSpace.Modules Y) (a : M ⟶ N)
      (m : (RingedSpace.moduleStalkFunctor Y (f x)).obj M),
      c N ((RingedSpace.moduleStalkFunctor Y (f x)).map a m) =
      PresheafOfModules.stalkAddMap
          (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a).val (c M m) := by sorry

end
