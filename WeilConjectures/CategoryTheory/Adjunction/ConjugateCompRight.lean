/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugateComp

/-!
# Right unit law of conjugate composition isomorphisms

`CategoryTheory.conjugateIsoEquiv_comp_right_hom_app`: if `c : L_F ≅ L_h ⋙ G` and `ι : G ≅ 𝟭`
compose to `e : L_F ≅ L_h`, then the conjugates `R_F ≅ R_G ⋙ R_h` of `c` and `R_G ≅ 𝟭` of `ι`
compose to the conjugate `R_F ≅ R_h` of `e`. This is the mirror image of
`CategoryTheory.conjugateIsoEquiv_comp_left_hom_app`.
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- Let `c : L_F ≅ L_h ⋙ G` and `ι : G ≅ 𝟭` be isomorphisms of left adjoints whose composite is
`e : L_F ≅ L_h`. Then the conjugates `R_F ≅ R_G ⋙ R_h` of `c` and `R_G ≅ 𝟭` of `ι` compose to
the conjugate `R_F ≅ R_h` of `e` (the right unit law of conjugate composition isomorphisms). -/
lemma conjugateIsoEquiv_comp_right_hom_app {LF Lh : C ⥤ D} {RF Rh : D ⥤ C} {G RG : D ⥤ D}
    (adjF : LF ⊣ RF) (adjh : Lh ⊣ Rh) (adjG : G ⊣ RG) (c : LF ≅ Lh ⋙ G) (ι : G ≅ 𝟭 D)
    (e : LF ≅ Lh) (hc : ∀ K, c.hom.app K ≫ ι.hom.app (Lh.obj K) = e.hom.app K) (K' : D) :
    (conjugateIsoEquiv adjF (adjh.comp adjG) c.symm).hom.app K' ≫
        Rh.map ((conjugateIsoEquiv adjG Adjunction.id ι.symm).hom.app K') =
      (conjugateIsoEquiv adjF adjh e.symm).hom.app K' := by
  apply (adjh.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    conjugateIsoEquiv_apply_hom, Iso.symm_hom, Adjunction.counit_naturality]
  have hι : (conjugateEquiv adjG Adjunction.id ι.inv).app K' =
      ι.inv.app (RG.obj K') ≫ adjG.counit.app K' := by
    simp [conjugateEquiv_apply_app]
  have hC := conjugateEquiv_counit adjF (adjh.comp adjG) c.inv K'
  have hE := conjugateEquiv_counit adjF adjh e.inv K'
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_counit_app] at hC
  have he : e.inv.app (RF.obj K') =
      ι.inv.app (Lh.obj (RF.obj K')) ≫ c.inv.app (RF.obj K') := by
    rw [← cancel_mono (e.hom.app _), Iso.inv_hom_id_app, Category.assoc, ← hc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rfl
  have hn₁ := ι.inv.naturality (Lh.map ((conjugateEquiv adjF (adjh.comp adjG) c.inv).app K'))
  have hn₂ := ι.inv.naturality (adjh.counit.app (RG.obj K'))
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj] at hn₁ hn₂ ⊢
  rw [hE, he, Category.assoc, ← hC, hι, ← reassoc_of% hn₁, ← reassoc_of% hn₂]

end CategoryTheory
