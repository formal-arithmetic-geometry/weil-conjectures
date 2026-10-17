/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Counits of conjugated composition isomorphisms

Let `L_F ⊣ R_F`, `L_h ⊣ R_h` and `G ⊣ R_G` be adjunctions, `c : L_F ≅ L_h ⋙ G` a composition
isomorphism of left adjoints and `ι : G ≅ 𝟭` an identity isomorphism. Their conjugates are a
composition isomorphism `R_F ≅ R_G ⋙ R_h` and an identity isomorphism `R_G ≅ 𝟭` of the right
adjoints. This file records how the counits interact with these conjugates; it is used for the
exceptional functors of the six-functor formalism, where `c` and `ι` are the composition and
identity isomorphisms of the lower shriek and their conjugates those of the upper shriek.

## Main results

- `CategoryTheory.conjugateIsoEquiv_comp_unit_counit`: if `c` composed with `ι` is an
  isomorphism `e : L_F ≅ L_h`, then the counit of `L_h ⊣ R_h`, composed with the conjugates of
  `c` and `ι`, is the counit of `L_F ⊣ R_F` transported along `e`.
- `CategoryTheory.Adjunction.counit_eqToHom_family`: transport of counits along an equality of
  indices in a family of adjunctions.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- Let `c : L_F ≅ L_h ⋙ G` and `ι : G ≅ 𝟭` be isomorphisms of left adjoints whose composite is
`e : L_F ≅ L_h`. Then, for the conjugates `R_F ≅ R_G ⋙ R_h` of `c` and `R_G ≅ 𝟭` of `ι`, the
composite `L_h R_F K ⟶ L_h R_h R_G K ⟶ R_G K ⟶ K` of the conjugate of `c`, the counit of
`L_h ⊣ R_h` and the conjugate of `ι` is `L_h R_F K ≅ L_F R_F K ⟶ K`. -/
lemma conjugateIsoEquiv_comp_unit_counit {LF Lh : C ⥤ D} {RF Rh : D ⥤ C} {G RG : D ⥤ D}
    (adjF : LF ⊣ RF) (adjh : Lh ⊣ Rh) (adjG : G ⊣ RG) (c : LF ≅ Lh ⋙ G) (ι : G ≅ 𝟭 D)
    (e : LF ≅ Lh) (hc : ∀ K, c.hom.app K ≫ ι.hom.app (Lh.obj K) = e.hom.app K) (K' : D) :
    Lh.map ((conjugateIsoEquiv adjF (adjh.comp adjG) c.symm).hom.app K') ≫
        adjh.counit.app (RG.obj K') ≫
        (conjugateIsoEquiv adjG Adjunction.id ι.symm).hom.app K' =
      e.inv.app (RF.obj K') ≫ adjF.counit.app K' := by
  have hι := conjugateEquiv_counit adjG Adjunction.id ι.inv K'
  have hC := conjugateEquiv_counit adjF (adjh.comp adjG) c.inv K'
  have he : ι.inv.app (Lh.obj (RF.obj K')) ≫ c.inv.app (RF.obj K') = e.inv.app (RF.obj K') := by
    rw [← cancel_mono (e.hom.app _), Category.assoc, Iso.inv_hom_id_app, ← hc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rfl
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Adjunction.id_counit,
    NatTrans.id_app, Category.comp_id] at hι
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_counit_app] at hC
  rw [conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_hom, Iso.symm_hom, Iso.symm_hom, hι,
    ← he, Category.assoc, ← hC]
  have h1 := ι.inv.naturality (adjh.counit.app (RG.obj K'))
  have h2 := ι.inv.naturality (Lh.map ((conjugateEquiv adjF (adjh.comp adjG) c.inv).app K'))
  simp only [Functor.id_obj, Functor.id_map] at h1 h2
  rw [reassoc_of% h1, reassoc_of% h2]

/-- Transport of counits along an equality `m = m'` of indices in a family of adjunctions
`L m ⊣ R m`. -/
lemma Adjunction.counit_eqToHom_family {M : Type*} (L : M → C ⥤ D) (R : M → D ⥤ C)
    (adj : ∀ m, L m ⊣ R m) {m m' : M} (hm : m = m') (K : D) :
    (L m').map (eqToHom (congrArg (fun n ↦ (R n).obj K) hm.symm)) ≫
        eqToHom (congrArg (fun n ↦ (L n).obj ((R m).obj K)) hm.symm) ≫ (adj m).counit.app K =
      (adj m').counit.app K := by
  subst hm
  simp

end CategoryTheory
