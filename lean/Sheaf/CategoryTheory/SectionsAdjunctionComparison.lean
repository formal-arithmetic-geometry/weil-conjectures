/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Sections comparisons and uniqueness of adjoints

Source: Stacks Project, Tag 07A6, composition of adjunctions.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory.Adjunction

/-- Transport of a composite constant-section adjunction recovers the prescribed
sections comparison, even if the first right adjoint is replaced by another one.
Source: Stacks Project, Tag 07A6.
(blueprint: lem-kun-sections-adjunction-comparison).

Proof: postcompose by the target sections-evaluation comparison and apply the
inverse evaluation Hom bijection. Naturality moves the source right-adjoint
comparison across the constants isomorphism. The right-adjoint counit identities
reduce both sides to the composite ordinary counit. The left-adjoint uniqueness
identity is exactly the remaining equality. -/
theorem sections_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {U : D ⥤ E} {R : E ⥤ D} {K : C ⥤ E}
    {S T V : D ⥤ C} {W X : E ⥤ C}
    (a : L ⊣ S) (b : L ⊣ T) (c : L ⊣ V)
    (d : K ⊣ W) (f : K ⊣ X) (p : U ⊣ R)
    (j : R ⋙ T ≅ X) (G : E) :
    (a.rightAdjointUniq c).hom.app (R.obj G) ≫
      (((c.comp p).ofNatIsoLeft
        (((b.comp p).ofNatIsoRight j).leftAdjointUniq f)).rightAdjointUniq d).hom.app G =
    (a.rightAdjointUniq b).hom.app (R.obj G) ≫ j.hom.app G ≫
      (d.rightAdjointUniq f).inv.app G := by
  let e := ((b.comp p).ofNatIsoRight j).leftAdjointUniq f
  apply (cancel_mono ((d.rightAdjointUniq f).hom.app G)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply (f.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [rightAdjointUniq_hom_app_counit, rightAdjointUniq_hom_app_counit,
    ofNatIsoLeft_counit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [e.inv.naturality_assoc]
  simp only [Functor.comp_map, comp_counit_app]
  rw [← U.map_comp_assoc, rightAdjointUniq_hom_app_counit]
  have he := leftAdjointUniq_hom_app_counit ((b.comp p).ofNatIsoRight j) f G
  simp only [ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    comp_counit_app] at he
  have he' : e.inv.app ((R ⋙ T).obj G) ≫ U.map (b.counit.app (R.obj G)) ≫
      p.counit.app G = K.map (j.hom.app G) ≫ f.counit.app G := by
    rw [← cancel_epi (e.hom.app ((R ⋙ T).obj G)), Iso.hom_inv_id_app_assoc]
    erw [← e.hom.naturality_assoc]
    rw [he]
    simp only [Functor.comp_map, ← U.map_comp_assoc, ← L.map_comp_assoc,
      Iso.hom_inv_id_app, L.map_id, Category.id_comp]
  rw [← he']
  erw [e.inv.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← U.map_comp_assoc, rightAdjointUniq_hom_app_counit]

end CategoryTheory.Adjunction
