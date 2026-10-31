/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Lifting a Frobenius isomorphism through fully faithful restriction

Source: latest blueprint, rem-dl-a1-conventions, the unramifiedness equivalence;
the categorical calculation in the proof of
`WeilSheaf.exists_isLisse_upperStar_iso_of_adicUpperStar_iso`.
(blueprint: lem-dl-a1-fully-faithful-frobenius-lift).
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

/-- A restriction identification transports a Frobenius isomorphism to an isomorphism
between two restricted objects. Bijectivity on morphisms lifts it and its inverse.

Source: rem-dl-a1-conventions, extension as a lisse Weil sheaf, proof step 6 of
lem-dl-a1-condensed-lisse-extension-inertia.
(blueprint: lem-dl-a1-fully-faithful-frobenius-lift).

Proof: form beta = c_L inverse followed by P_U(e), theta, and e inverse.
Lift beta and beta inverse using surjectivity on the two Hom sets. Their composites
are identities by injectivity on endomorphisms, giving alpha. Substitute its image
into c_L followed by J(alpha) and e; cancellation gives the displayed equation.
No essential-surjectivity assertion and no invariance of an integral lattice are needed.
-/
theorem exists_frobenius_iso_of_map_bijective
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : C ⥤ D) (PC : C ⥤ C) (PU : D ⥤ D)
    (c : J ⋙ PU ≅ PC ⋙ J) (P : C → Prop)
    (hJ : ∀ X Y, P X → P Y →
      Function.Bijective (J.map : (X ⟶ Y) → (J.obj X ⟶ J.obj Y)))
    {L : C} (hL : P L) (hPL : P (PC.obj L))
    {F : D} (θ : PU.obj F ≅ F) (e : J.obj L ≅ F) :
    ∃ α : PC.obj L ≅ L,
      PU.map e.hom ≫ θ.hom = c.hom.app L ≫ J.map α.hom ≫ e.hom := by
  let β : J.obj (PC.obj L) ≅ J.obj L :=
    (c.app L).symm ≪≫ PU.mapIso e ≪≫ θ ≪≫ e.symm
  obtain ⟨f, hf⟩ := (hJ (PC.obj L) L hPL hL).2 β.hom
  obtain ⟨g, hg⟩ := (hJ L (PC.obj L) hL hPL).2 β.inv
  have hfg : f ≫ g = 𝟙 (PC.obj L) := (hJ _ _ hPL hPL).1 (by
    simp only [J.map_comp, hf, hg, β.hom_inv_id, J.map_id])
  have hgf : g ≫ f = 𝟙 L := (hJ _ _ hL hL).1 (by
    simp only [J.map_comp, hf, hg, β.inv_hom_id, J.map_id])
  refine ⟨⟨f, g, hfg, hgf⟩, ?_⟩
  change PU.map e.hom ≫ θ.hom = c.hom.app L ≫ J.map f ≫ e.hom
  rw [hf]
  simp [β, Category.assoc]

end CategoryTheory
