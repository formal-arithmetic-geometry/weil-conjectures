/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Adjunction from a relative natural Hom chain

Source: blueprint det-def-sf-operations (vi), restriction of the finite etale Hom chain.
(blueprint: lem-sf-normalized-fully-faithful-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory

namespace CategoryTheory

/-- A natural Hom equivalence on the images of fully faithful realizations restricts
to an adjunction, with precisely the specified realization isomorphisms in its Hom
formula. No adjunction is required on the ambient categories.

Source: blueprint det-def-sf-operations (vi), finite coefficient Hom adjunction.
(blueprint: lem-sf-normalized-fully-faithful-adjunction).

Proof: map a morphism by RY, precompose with rF inverse, apply the relative Hom
chain, postcompose with rG inverse, and take the RX preimage. Each operation is
a bijection, so their composite is a bijection. To check source naturality, apply
faithful RX and postcompose with rG; naturality of rF and the Hom chain gives the
equality. Target naturality follows in the same way using rG and target naturality
of the Hom chain. Apply Adjunction.mkOfHomEquiv. Cancellation of rG inverse with
rG gives exactly the displayed normalization. This works also for empty categories. -/
theorem normalizedFullyFaithfulAdjunction
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (RX : C ⥤ C') (RY : D ⥤ D') [RX.Full] [RX.Faithful] [RY.Full] [RY.Faithful]
    (P : C' ⥤ D') (H : D' ⥤ C') (F : C ⥤ D) (G : D ⥤ C)
    (rF : F ⋙ RY ≅ RX ⋙ P) (rG : G ⋙ RX ≅ RY ⋙ H)
    (e : ∀ K L, (P.obj (RX.obj K) ⟶ RY.obj L) ≃ (RX.obj K ⟶ H.obj (RY.obj L)))
    (hleft : ∀ {K K'} (s : K ⟶ K') (L) (a : P.obj (RX.obj K') ⟶ RY.obj L),
      e K L (P.map (RX.map s) ≫ a) = RX.map s ≫ e K' L a)
    (hright : ∀ (K) {L L'} (a : P.obj (RX.obj K) ⟶ RY.obj L) (b : L ⟶ L'),
      e K L' (a ≫ RY.map b) = e K L a ≫ H.map (RY.map b)) :
    ∃ adj : F ⊣ G, ∀ K L (a : F.obj K ⟶ L),
      RX.map (adj.homEquiv K L a) ≫ rG.hom.app L =
        e K L (rF.inv.app K ≫ RY.map a) := by
  let ffX := Functor.FullyFaithful.ofFullyFaithful RX
  let ffY := Functor.FullyFaithful.ofFullyFaithful RY
  let ψ (K : C) (L : D) : (F.obj K ⟶ L) ≃ (K ⟶ G.obj L) :=
    ffY.homEquiv.trans (((rF.app K).homFromEquiv.trans (e K L)).trans
      (((rG.app L).symm.homToEquiv).trans ffX.homEquiv.symm))
  have hn (K : C) (L : D) (a : F.obj K ⟶ L) :
      RX.map (ψ K L a) ≫ rG.hom.app L =
        e K L (rF.inv.app K ≫ RY.map a) := by
    dsimp only [ψ, Equiv.trans_apply, Functor.FullyFaithful.homEquiv,
      Iso.homFromEquiv, Iso.homToEquiv, Equiv.symm, Equiv.coe_fn_mk]
    rw [ffX.map_preimage]
    simp only [Category.assoc]
    change e K L (rF.inv.app K ≫ RY.map a) ≫ rG.inv.app L ≫ rG.hom.app L = _
    rw [Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hl {K K' : C} (s : K ⟶ K') (L : D) (a : F.obj K' ⟶ L) :
      ψ K L (F.map s ≫ a) = s ≫ ψ K' L a := by
    apply RX.map_injective
    apply (cancel_mono (rG.hom.app L)).1
    rw [hn, RX.map_comp, Category.assoc, hn]
    have hnat := rF.inv.naturality s
    dsimp only [Functor.comp_map] at hnat
    rw [RY.map_comp, ← Category.assoc, ← hnat, Category.assoc]
    change e K L ((RX ⋙ P).map s ≫ rF.inv.app K' ≫ RY.map a) = _
    exact hleft s L _
  have hr (K : C) {L L' : D} (a : F.obj K ⟶ L) (b : L ⟶ L') :
      ψ K L' (a ≫ b) = ψ K L a ≫ G.map b := by
    apply RX.map_injective
    apply (cancel_mono (rG.hom.app L')).1
    have hnat := rG.hom.naturality b
    dsimp only [Functor.comp_map] at hnat
    rw [hn, RX.map_comp, Category.assoc, hnat]
    change _ = RX.map (ψ K L a) ≫ rG.hom.app L ≫ H.map (RY.map b)
    rw [← Category.assoc, hn, RY.map_comp, ← Category.assoc, hright]
  let core : Adjunction.CoreHomEquiv F G :=
    { homEquiv := ψ
      homEquiv_naturality_left_symm := by
        intro K K' L s a
        apply (ψ K L).injective
        rw [Equiv.apply_symm_apply, hl, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun {_ _ _} a b ↦ hr _ a b }
  exact ⟨Adjunction.mkOfHomEquiv core, fun K L a ↦ by
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    change RX.map (ψ K L a) ≫ rG.hom.app L = _
    exact hn K L a⟩

end CategoryTheory
