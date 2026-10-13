/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor

/-!
# Ext identity comparison

Source: Stacks Project, derived.tex, Tag 015F; Mathlib Ext.Map.
(blueprint: lem-weil-pbc-ext-exact-functor-identity-comparison)
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

/-- An exact functor isomorphic to the identity acts on Ext by that comparison.
Source: Stacks Project, derived.tex, Tag 015F, and Mathlib Ext.Map.
(blueprint: lem-weil-pbc-ext-exact-functor-identity-comparison)

Proof: by `mapExactFunctor_eq_of_iso`, pushing forward along `𝟭 C` is conjugate by `e` to
pushing forward along `F`, and pushing forward along `𝟭 C` is the identity
(`mapExactFunctor_id`). -/
theorem exactFunctorIdentityComparison
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
    (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp x (zero_add n) := by
  have h := mapExactFunctor_eq_of_iso (D := C) e x
  rw [mapExactFunctor_id] at h
  conv_rhs => rw [h]
  rw [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, Iso.hom_inv_id_app, mk₀_id_comp]

end CategoryTheory.Abelian.Ext
