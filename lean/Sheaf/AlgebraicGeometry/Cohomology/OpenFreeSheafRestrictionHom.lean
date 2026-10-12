/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisFreeComplex
/-! # Restriction of morphisms from a represented open

Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Restriction is bijective on morphisms out of the free sheaf of the image open.
Source: Stacks Project, Tags 03DI and 03DJ; the represented free-sheaf adjunction.
(blueprint: lem-pc-open-free-restriction-hom)

Proof: The represented free sheaf of j.opensRange is extension by zero of the
constant free rank-one abelian sheaf on Y. This follows by applying the Yoneda,
free/forgetful, and sheafification adjunctions: both objects represent sections on
the image open. Restricting this extension gives the original sheaf; the unit of
the extension/restriction adjunction is an isomorphism. Its adjunction bijection
is restriction on morphisms, followed by precomposition with this unit. Since
the unit is invertible, restriction itself is bijective. This also holds for the
empty open, where the source is zero, and for the top open, where j is an
isomorphism. The coefficient sheaf F is arbitrary.
-/
theorem H.openFreeSheaf_restrictionHom_bijective {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Function.Bijective (fun a : H.openFreeSheaf j.opensRange ⟶ F =>
      (invImage j).map a) := by sorry

end AlgebraicGeometry.Scheme.Modules
