/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Ring.Limits

/-! # Integer-graded left modules on a ringed site

Source: Stacks Project, sdga.tex, Tags 0FQW and 0FQZ, and section-localize-graded.
(blueprint: def-sfb-graded-ringed-site).

There are no differentials and no commutativity condition on the graded algebra.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c h r m
open CategoryTheory Opposite
namespace CategoryTheory.GradedRingedSite
variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}

/-- Forget only commutativity of the coefficient sheaf.
Source: Stacks, Tag 0FQZ (blueprint: def-sfb-graded-ringed-site). -/
abbrev rings (R : Sheaf J CommRingCat.{max c h r}) : Sheaf J RingCat.{max c h r} :=
  (sheafCompose J (forget₂ CommRingCat.{max c h r} RingCat.{max c h r})).obj R

/-- An associative unital integer-graded algebra of module sheaves.
Source: Stacks, definition-ga (blueprint: def-sfb-graded-ringed-site). -/
structure Algebra (R : Sheaf J CommRingCat.{max c h r}) where
  degree : ℤ → ringedSiteModules.{m} (rings R)
  mul (i j : ℤ) (V : Cᵒᵖ) :
    (degree i).val.obj V →ₗ[R.obj.obj V]
      (degree j).val.obj V →ₗ[R.obj.obj V] (degree (i + j)).val.obj V
  one (V : Cᵒᵖ) : (degree 0).val.obj V
  one_natural {V W : Cᵒᵖ} (f : V ⟶ W) : (degree 0).val.map f (one V) = one W
  mul_natural (i j : ℤ) {V W : Cᵒᵖ} (f : V ⟶ W)
      (a : (degree i).val.obj V) (b : (degree j).val.obj V) :
    (degree (i + j)).val.map f (mul i j V a b) =
      mul i j W ((degree i).val.map f a) ((degree j).val.map f b)
  assoc (i j k : ℤ) (V : Cᵒᵖ) (a : (degree i).val.obj V)
      (b : (degree j).val.obj V) (d : (degree k).val.obj V) :
    HEq (mul (i + j) k V (mul i j V a b) d) (mul i (j + k) V a (mul j k V b d))
  one_mul (i : ℤ) (V : Cᵒᵖ) (a : (degree i).val.obj V) :
    HEq (mul 0 i V (one V) a) a
  mul_one (i : ℤ) (V : Cᵒᵖ) (a : (degree i).val.obj V) :
    HEq (mul i 0 V a (one V)) a

/-- Graded left module sheaves, with no differential.
Source: Stacks, Tag 0FQZ, left analogue (blueprint: def-sfb-graded-ringed-site). -/
structure Module {R : Sheaf J CommRingCat.{max c h r}} (A : Algebra.{c, h, r, m} R) where
  degree : ℤ → ringedSiteModules.{m} (rings R)
  act (i q : ℤ) (V : Cᵒᵖ) :
    (A.degree i).val.obj V →ₗ[R.obj.obj V]
      (degree q).val.obj V →ₗ[R.obj.obj V] (degree (i + q)).val.obj V
  act_natural (i q : ℤ) {V W : Cᵒᵖ} (f : V ⟶ W)
      (a : (A.degree i).val.obj V) (x : (degree q).val.obj V) :
    (degree (i + q)).val.map f (act i q V a x) =
      act i q W ((A.degree i).val.map f a) ((degree q).val.map f x)
  assoc (i j q : ℤ) (V : Cᵒᵖ) (a : (A.degree i).val.obj V)
      (b : (A.degree j).val.obj V) (x : (degree q).val.obj V) :
    HEq (act (i + j) q V (A.mul i j V a b) x) (act i (j + q) V a (act j q V b x))
  one_act (q : ℤ) (V : Cᵒᵖ) (x : (degree q).val.obj V) :
    HEq (act 0 q V (A.one V) x) x

/-- Degree-zero, action-preserving linear sheaf maps.
Source: Stacks, Tag 0FQZ (blueprint: def-sfb-graded-ringed-site). -/
structure Hom {R : Sheaf J CommRingCat.{max c h r}} {A : Algebra.{c, h, r, m} R}
    (M N : Module.{c, h, r, m} A) where
  degree (q : ℤ) : M.degree q ⟶ N.degree q
  action (i q : ℤ) (V : Cᵒᵖ) (a : (A.degree i).val.obj V)
      (x : (M.degree q).val.obj V) :
    (degree (i + q)).val.app V (M.act i q V a x) =
      N.act i q V a ((degree q).val.app V x)

/-- Composition and identity are degreewise composition and identity.
Source: Stacks, Tag 0FQZ (blueprint: def-sfb-graded-ringed-site). -/
instance moduleCategory {R : Sheaf J CommRingCat.{max c h r}} (A : Algebra.{c, h, r, m} R) :
    Category (Module.{c, h, r, m} A) where
  Hom := Hom
  id M := ⟨fun q ↦ 𝟙 (M.degree q), fun _ _ _ _ _ ↦ rfl⟩
  comp f g := ⟨fun q ↦ f.degree q ≫ g.degree q, fun i q V a x ↦ by
    change (g.degree (i + q)).val.app V
      ((f.degree (i + q)).val.app V (Module.act _ i q V a x)) = _
    rw [f.action, g.action]
    rfl⟩
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g k := by cases f; cases g; cases k; rfl

/-- The degree evaluation functor.
Source: Stacks, Tag 0FQZ (blueprint: def-sfb-graded-ringed-site). -/
def evaluation {R : Sheaf J CommRingCat.{max c h r}} (A : Algebra.{c, h, r, m} R) (q : ℤ) :
    Module.{c, h, r, m} A ⥤ ringedSiteModules.{m} (rings R) where
  obj M := M.degree q
  map f := f.degree q

/-- Restrict a graded algebra to the localized site.
Source: Stacks, section-localize-graded (blueprint: def-sfb-graded-ringed-site). -/
def Algebra.over {R : Sheaf J CommRingCat.{max c h r}} (A : Algebra.{c, h, r, m} R) (U : C) :
    Algebra.{max c h, h, r, m} (R.over U) where
  degree q := (A.degree q).over U
  mul i j V := A.mul i j (op V.unop.left)
  one V := A.one (op V.unop.left)
  one_natural f := A.one_natural ((Over.forget U).op.map f)
  mul_natural i j := fun {_ _} f a b ↦ A.mul_natural i j ((Over.forget U).op.map f) a b
  assoc i j k V a b d := A.assoc i j k (op V.unop.left) a b d
  one_mul i V a := A.one_mul i (op V.unop.left) a
  mul_one i V a := A.mul_one i (op V.unop.left) a

/-- Degreewise restriction of a graded module.
Source: Stacks, section-localize-graded (blueprint: def-sfb-graded-ringed-site). -/
def Module.over {R : Sheaf J CommRingCat.{max c h r}} {A : Algebra.{c, h, r, m} R}
    (M : Module.{c, h, r, m} A) (U : C) : Module.{max c h, h, r, m} (A.over U) where
  degree q := (M.degree q).over U
  act i q V := M.act i q (op V.unop.left)
  act_natural i q := fun {_ _} f a x ↦ M.act_natural i q ((Over.forget U).op.map f) a x
  assoc i j q V a b x := M.assoc i j q (op V.unop.left) a b x
  one_act q V x := M.one_act q (op V.unop.left) x

/-- Restriction of graded modules and degree-zero maps.
Source: Stacks, section-localize-graded (blueprint: def-sfb-graded-ringed-site). -/
def restriction {R : Sheaf J CommRingCat.{max c h r}} (A : Algebra.{c, h, r, m} R) (U : C) :
    Module.{c, h, r, m} A ⥤ Module.{max c h, h, r, m} (A.over U) where
  obj M := M.over U
  map f := ⟨fun q ↦ (f.degree q).over U,
    fun i q V a x ↦ f.action i q (op V.unop.left) a x⟩

end CategoryTheory.GradedRingedSite
