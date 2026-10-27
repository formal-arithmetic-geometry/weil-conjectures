/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Yoneda

/-! # Counit-normalized transport across equivalences

Source: finite-ring site tensor transpose, proof step 4
(blueprint: lem-pur-finite-ring-adjoint-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The mate of a square whose vertical functors are equivalences is invertible,
and is uniquely determined by its counit equation.

Source: proof step 4 of lem-pur-finite-ring-site-tensor-transpose and uniqueness of
right adjoints, Mathlib `Adjunction.rightAdjointUniq`
(blueprint: lem-pur-finite-ring-adjoint-transport).

Proof: transpose the inverse square followed by the image of the first counit under
the second adjunction. Naturality of the square and counit makes these transposes
natural. On Hom sets from objects in the image of the first equivalence, composition
with this mate is the composite of full-faithfulness bijections, the two adjunction
bijections and the square isomorphism. It is bijective. Essential surjectivity extends
this to every test object; Yoneda gives invertibility. The inverse adjunction bijection
gives the counit equation and shows that any other solution has identical components. -/
theorem finiteRingAdjointTransport
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    (E : C ⥤ C') (H : D ⥤ D') [E.IsEquivalence] [H.IsEquivalence]
    (F : C ⥤ D) (R : D ⥤ C) (a : F ⊣ R)
    (F' : C' ⥤ D') (G : D' ⥤ C') (a' : F' ⊣ G)
    (b : F ⋙ H ≅ E ⋙ F') :
    ∃! rho : R ⋙ E ≅ H ⋙ G,
      ∀ L, b.hom.app (R.obj L) ≫ F'.map (rho.hom.app L) ≫
        a'.counit.app (H.obj L) = H.map (a.counit.app L) := by
  let t : R ⋙ E ⟶ H ⋙ G :=
    { app L := a'.homEquiv _ _ (b.inv.app (R.obj L) ≫ H.map (a.counit.app L))
      naturality L L' f := by
        dsimp only [Functor.comp_map]
        rw [← a'.homEquiv_naturality_left, ← a'.homEquiv_naturality_right]
        apply congrArg (a'.homEquiv _ _)
        have hn := b.inv.naturality (R.map f)
        dsimp only [Functor.comp_map] at hn
        rw [← Category.assoc, hn, Category.assoc]
        rw [Category.assoc, ← H.map_comp]
        have hε := a.counit.naturality f
        dsimp only [Functor.comp_map, Functor.id_map] at hε
        rw [hε, H.map_comp] }
  have ht (L : D) : F'.map (t.app L) ≫ a'.counit.app (H.obj L) =
      b.inv.app (R.obj L) ≫ H.map (a.counit.app L) := by
    exact (a'.homEquiv _ _).symm_apply_apply _
  have hi (L : D) : IsIso (t.app L) := by
    apply isIso_of_yoneda_map_bijective
    intro N
    let M := E.objPreimage N
    let i : E.obj M ≅ N := E.objObjPreimageIso N
    let e : (E.obj M ⟶ E.obj (R.obj L)) ≃ (E.obj M ⟶ G.obj (H.obj L)) :=
      (Functor.FullyFaithful.ofFullyFaithful E).homEquiv.symm |>.trans
        ((a.homEquiv M L).symm.trans
          ((Functor.FullyFaithful.ofFullyFaithful H).homEquiv.trans
            ((Iso.homCongr (b.app M) (Iso.refl _)).trans (a'.homEquiv _ _))))
    have he (g : E.obj M ⟶ E.obj (R.obj L)) : e g = g ≫ t.app L := by
      let f := E.preimage g
      have hf : E.map f = g := E.map_preimage g
      change a'.homEquiv _ _
        (b.inv.app M ≫ H.map ((a.homEquiv M L).symm f) ≫ 𝟙 _) = _
      rw [Category.comp_id, Adjunction.homEquiv_counit, H.map_comp]
      have hn := b.inv.naturality f
      dsimp only [Functor.comp_map] at hn
      rw [← Category.assoc, ← hn, Category.assoc, a'.homEquiv_naturality_left]
      rw [hf]
      rfl
    let pre₁ : (N ⟶ E.obj (R.obj L)) ≃ (E.obj M ⟶ E.obj (R.obj L)) :=
      Iso.homCongr i.symm (Iso.refl _)
    let pre₂ : (N ⟶ G.obj (H.obj L)) ≃ (E.obj M ⟶ G.obj (H.obj L)) :=
      Iso.homCongr i.symm (Iso.refl _)
    have heq : (fun g : N ⟶ E.obj (R.obj L) ↦ g ≫ t.app L) =
        ((pre₁.trans e).trans pre₂.symm) := by
      funext g
      simp only [Equiv.trans_apply, he, pre₁, pre₂, Iso.homCongr_apply,
        Iso.symm_inv, Iso.refl_hom, Category.comp_id]
      simp [Category.assoc]
    change Function.Bijective (fun g : N ⟶ E.obj (R.obj L) ↦ g ≫ t.app L)
    exact heq.symm ▸ ((pre₁.trans e).trans pre₂.symm).bijective
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨asIso t, ?_, ?_⟩
  · intro L
    change b.hom.app (R.obj L) ≫ F'.map (t.app L) ≫ _ = _
    simpa only [Category.assoc, b.hom_inv_id_app_assoc] using
      congrArg (fun z ↦ b.hom.app (R.obj L) ≫ z) (ht L)
  · intro sigma hs
    apply Iso.ext
    apply NatTrans.ext
    funext L
    apply (a'.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    apply (cancel_epi (b.hom.app (R.obj L))).1
    simpa only [Category.assoc] using (hs L).trans
      (by
        change _ = b.hom.app (R.obj L) ≫ F'.map (t.app L) ≫ _
        simpa only [Category.assoc, b.hom_inv_id_app_assoc] using
          (congrArg (fun z ↦ b.hom.app (R.obj L) ≫ z) (ht L)).symm)

/-- The counit-normalized comparison carries every adjoint transpose to its
transported transpose. Source: proof step 10 of the finite-ring site transport
(blueprint: lem-pur-finite-ring-adjoint-transport).

Proof: apply the inverse Hom equivalence of the second adjunction. Expand it as
left-adjoint application followed by counit, use the counit normalization, and move
the first transpose through the natural comparison square. The first adjunction's
counit equation then leaves the original morphism. -/
theorem finiteRingAdjointTransport_transpose
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    (E : C ⥤ C') (H : D ⥤ D')
    (F : C ⥤ D) (R : D ⥤ C) (a : F ⊣ R)
    (F' : C' ⥤ D') (G : D' ⥤ C') (a' : F' ⊣ G)
    (b : F ⋙ H ≅ E ⋙ F') (rho : R ⋙ E ⟶ H ⋙ G)
    (hc : ∀ L, b.hom.app (R.obj L) ≫ F'.map (rho.app L) ≫
      a'.counit.app (H.obj L) = H.map (a.counit.app L))
    (M : C) (L : D) (v : F.obj M ⟶ L) :
    E.map (a.homEquiv M L v) ≫ rho.app L =
      a'.homEquiv _ _ (b.inv.app M ≫ H.map v) := by
  have hc' (L : D) : F'.map (rho.app L) ≫ a'.counit.app (H.obj L) =
      b.inv.app (R.obj L) ≫ H.map (a.counit.app L) := by
    rw [← hc L]
    simp only [← Category.assoc, b.inv_hom_id_app, Category.id_comp]
  apply (a'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, F'.map_comp, Category.assoc, hc']
  have hn := b.inv.naturality (a.homEquiv M L v)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← H.map_comp]
  congr 2
  exact (a.homEquiv M L).symm_apply_apply v

end AlgebraicGeometry.ProEtale
