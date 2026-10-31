/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Iso

/-! Cancellation through isomorphisms on both sides of a categorical arrow. -/

@[expose] public section
open CategoryTheory

/-- Equality remains after cancelling an isomorphism on the source and target.
Source: the cancellation step in the normalized cofinal-support composition.
(blueprint: lem-pur-etale-cofinal-support-iso-cancellation). -/
theorem CategoryTheory.cancel_iso_whiskers
    {C : Type*} [Category C] {A B : C} (e : A ≅ B)
    {D E : C} (d : D ≅ E) (u v : B ⟶ D)
    (h : e.hom ≫ u ≫ d.hom = e.hom ≫ v ≫ d.hom) : u = v := by
  apply (cancel_epi e.hom).1
  apply (cancel_mono d.hom).1
  simpa only [Category.assoc] using h
