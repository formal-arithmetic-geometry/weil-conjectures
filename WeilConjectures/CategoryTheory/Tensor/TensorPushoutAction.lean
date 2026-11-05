/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Scalar actions on a sheafified balanced tensor product

The sectionwise tensor action extends through sheafification. Its normalization
on the two scalar factors determines it uniquely.

Source: Stacks Project, Tag 03EK.
(blueprint: lem-pur-tensor-pushout-action)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u vC uC
open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings
namespace CategoryTheory

section
variable {A B R V : Type u} [CommRing A] [CommRing B] [CommRing R]
  [AddCommGroup V] [Module R V] (a : A →+* R) (b : A →+* B)

end

section Sheaf
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B R T : Sheaf J CommRingCat.{u}} (a : A ⟶ R) (b : A ⟶ B)
  (c : R ⟶ T) (d : B ⟶ T)
  (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

end Sheaf
end CategoryTheory
