/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.ProperBaseChange.GeometricModuleConstruction
import all WeilConjectures.ProperBaseChange.GeometricModuleTransport
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Scalar extension and inverse image on independently sized sites

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03EL.
(blueprint: lem-per-independent-scalar-inverse-image).
-/

@[expose] public noncomputable section
universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SheafOfModules.GeometricConstruction
namespace SheafOfModules.ScalarIndependent
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

private abbrev ringSheaf {C : Type uC} [Category.{vC} C]
    [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
private abbrev restriction {C : Type uC} [Category.{vC} C]
    [EssentiallySmall.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    SheafOfModules.{u} (ringSheaf S) ⥤ SheafOfModules.{u} (ringSheaf R) :=
  restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map a)

attribute [local instance] sheafBinaryProduct

attribute [local irreducible] productInverse

/- Elementary operation graphs, used directly without the general tensor or
K-flat pullback constructions. Source: the operation-transport calculations in
RingedToposKFlatPullback and RingedTopoiInverseImageTensorPairingIsIso. -/

attribute [local irreducible] mateIsoEquiv restrictHomEquiv

set_option maxHeartbeats 800000 in
-- Elaborating the operation-preserving Hom equivalence has many dependent objects.
set_option Elab.async false in
attribute [local irreducible] madd msmul
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000 in
-- The unit equation compares two adjunctions and two restriction functors.
end SheafOfModules.ScalarIndependent
