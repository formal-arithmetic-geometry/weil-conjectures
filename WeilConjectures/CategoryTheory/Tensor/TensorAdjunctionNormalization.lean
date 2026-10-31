/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Normalizing a tensor right adjunction at a unit object -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory.MonoidalCategory
namespace CategoryTheory

private theorem lift_tensor_auto
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    (P : C ⥤ D) (H : D ⥤ D) [H.Full] [H.Faithful]
    (I : C) (L : D) (u : P.obj I ≅ 𝟙_ D)
    (k : ((P ⋙ tensorRight L) ⋙ H).obj I ≅ ((P ⋙ tensorRight L) ⋙ H).obj I) :
    ∃ h : ((P ⋙ tensorRight L) ⋙ H) ≅ ((P ⋙ tensorRight L) ⋙ H),
      h.hom.app I = k.hom := by
  let v := (tensorRight L).mapIso u ≪≫ λ_ L
  let w := H.mapIso v
  let e := H.preimageIso (w.symm ≪≫ k ≪≫ w)
  let h := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft P ((curriedTensor D).flip.mapIso e)) H
  refine ⟨h, ?_⟩
  change H.map (P.obj I ◁ e.hom) = k.hom
  have hv : (P.obj I ◁ e.hom) ≫ v.hom = v.hom ≫ e.hom := by
    dsimp only [v, Iso.trans_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    change (P.obj I ◁ e.hom) ≫ u.hom ▷ L ≫ (λ_ L).hom =
      u.hom ▷ L ≫ (λ_ L).hom ≫ e.hom
    rw [whisker_exchange_assoc, leftUnitor_naturality]
  apply (cancel_mono w.hom).mp
  change H.map (P.obj I ◁ e.hom) ≫ H.map v.hom = k.hom ≫ w.hom
  rw [← H.map_comp, hv, H.map_comp]
  simp only [e, Functor.preimageIso_hom, H.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom]
  change w.hom ≫ w.inv ≫ k.hom ≫ w.hom = k.hom ≫ w.hom
  rw [Iso.hom_inv_id_assoc]

private theorem rightAdjointUniq_transport
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G R : D ⥤ C} (a : F ⊣ G) (b : F ⊣ R) (h : G ≅ G) :
    (b.rightAdjointUniq (a.ofNatIsoRight h)).hom =
      (b.rightAdjointUniq a).hom ≫ h.hom := by
  ext K
  apply ((a.ofNatIsoRight h).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  simp only [NatTrans.comp_app, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]

/-- Normalize the coefficient component of a tensor-and-shift right adjunction.
Source: sk-thm-dnc, Local construction, affine-space adjunction and its unit orientation
(blueprint: lem-trf-tensor-right-adjunction-normalization).

Proof: Let G be P followed by tensoring with L and then H. The isomorphism u, the left
unitor, and full faithfulness of H identify automorphisms of G(I) with automorphisms of
L. Tensoring by such an automorphism and whiskering by P and H extends it naturally
to G. If e is the existing right-adjoint uniqueness component followed by q, extend
the automorphism q followed by z followed by e followed by q inverse. Transport the
adjunction by the inverse natural automorphism. The right-adjoint uniqueness formula
shows that the new component followed by q and z is identity; hence its inverse is z.
-/
theorem tensorRightAdjunction_normalize
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    (P : C ⥤ D) (H : D ⥤ D) [H.Full] [H.Faithful]
    (I : C) (L M : D) (u : P.obj I ≅ 𝟙_ D)
    {F : D ⥤ C} {R : C ⥤ D}
    (a : F ⊣ ((P ⋙ tensorRight L) ⋙ H)) (b : F ⊣ R)
    (q : ((P ⋙ tensorRight L) ⋙ H).obj I ≅ M) (z : M ≅ R.obj I) :
    ∃ adj : F ⊣ ((P ⋙ tensorRight L) ⋙ H),
      ((b.rightAdjointUniq adj).app I ≪≫ q).inv = z.hom := by
  let e := (b.rightAdjointUniq a).app I ≪≫ q
  let k := q ≪≫ z ≪≫ e ≪≫ q.symm
  obtain ⟨h, hh⟩ := lift_tensor_auto P H I L u k
  let adj := a.ofNatIsoRight h.symm
  refine ⟨adj, ?_⟩
  have he : e.hom = (b.rightAdjointUniq a).hom.app I ≫ q.hom := by rfl
  have hn : ((b.rightAdjointUniq adj).app I ≪≫ q).hom ≫ z.hom = 𝟙 _ := by
    change ((b.rightAdjointUniq adj).hom.app I ≫ q.hom) ≫ z.hom = 𝟙 _
    rw [rightAdjointUniq_transport a b h.symm]
    simp only [NatTrans.comp_app, Iso.symm_hom, Category.assoc]
    have hk : h.hom.app I = q.hom ≫ z.hom ≫ e.hom ≫ q.inv := by
      simpa only [k, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hh
    rw [he] at hk
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hk
    apply (cancel_mono ((b.rightAdjointUniq a).hom.app I)).mp
    simp only [Category.assoc, Category.id_comp]
    rw [← hk, Iso.inv_hom_id_app, Category.comp_id]
  apply (cancel_epi ((b.rightAdjointUniq adj).app I ≪≫ q).hom).mp
  rw [Iso.hom_inv_id]
  exact hn.symm

end CategoryTheory
