/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Iso

/-! # Composition of nonempty isomorphism types -/

@[expose] public section
set_option autoImplicit false
namespace CategoryTheory

/-- Two existing isomorphisms compose without choosing a public map.
Source: Mathlib CategoryTheory.Iso.trans
(blueprint: lem-exc-nonempty-iso-composition).

Proof: eliminate the two Nonempty proofs in the propositional target. Compose
the resulting isomorphisms with Iso.trans and package the result in Nonempty.
The inverse is the reverse composite; its two inverse identities are those of
Iso.trans. No isomorphism is defined by choice. -/
theorem nonempty_iso_comp
    {C : Type*} [Category C] {x y z : C}
    (h : Nonempty (x ≅ y)) (k : Nonempty (y ≅ z)) : Nonempty (x ≅ z) := by
  obtain ⟨e⟩ := h
  obtain ⟨q⟩ := k
  exact ⟨e ≪≫ q⟩

end CategoryTheory
