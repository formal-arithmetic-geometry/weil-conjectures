/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Signed dual and Hom into a single sheaf

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-to-single).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R : Sheaf J CommRingCat.{u}}

private lemma homObjMap_zero_target {M N N' : SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (f : M ⟶ M) :
    SheafOfModules.homObjMap (R := R) f (0 : N ⟶ N') = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
  ext W x
  rfl

private lemma isIso_dependent {D : Type*} [Category D] {A : D} {B : ℤ → D}
    {k : ℤ} (π : ∀ q, k = q → (A ⟶ B q)) {q : ℤ} (hq : k = q)
    (hi : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact hi


end CategoryTheory
