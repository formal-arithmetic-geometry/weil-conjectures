/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Mates of 2-squares along identity adjunctions

Let `u_X ⊣ s_X` and `u_S ⊣ s_S` be adjunctions whose functors are identified with identity
functors, `ι : u ≅ 𝟭` and `κ : s ≅ 𝟭`, compatibly with the units. A 2-square
`α : s_X ⋙ F ⟶ F ⋙ s_S` which is the identity through `κ` has as mate
`F ⋙ u_S ⟶ u_X ⋙ F` the identity through `ι`
(`CategoryTheory.mateEquiv_symm_app_eq_of_id`). In the six-functor formalism this computes the
compact-support base change `Ex_!` of a square whose horizontal morphisms are identities.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- Let `u_X ⊣ s_X` on `C` and `u_S ⊣ s_S` on `D` be adjunctions with isomorphisms
`ι_X : u_X ≅ 𝟭`, `κ_X : s_X ≅ 𝟭` (and the same on `D`) compatible with the units. If a 2-square
`α : s_X ⋙ F ⟶ F ⋙ s_S` is `F κ_X` through `κ_S`, its mate `F ⋙ u_S ⟶ u_X ⋙ F` is
`ι_S F ≫ F ι_X⁻¹`. -/
lemma mateEquiv_symm_app_eq_of_id {uX sX : C ⥤ C} (adjX : uX ⊣ sX) {uS sS : D ⥤ D}
    (adjS : uS ⊣ sS) (ιX : uX ≅ 𝟭 C) (κX : sX ≅ 𝟭 C) (ιS : uS ≅ 𝟭 D) (κS : sS ≅ 𝟭 D)
    (hX : ∀ c, adjX.unit.app c ≫ κX.hom.app (uX.obj c) = ιX.inv.app c)
    (hS : ∀ d, adjS.unit.app d ≫ κS.hom.app (uS.obj d) = ιS.inv.app d)
    (F : C ⥤ D) (α : sX ⋙ F ⟶ F ⋙ sS)
    (hα : ∀ c, α.app c ≫ κS.hom.app (F.obj c) = F.map (κX.hom.app c)) (c : C) :
    ((mateEquiv adjX adjS).symm α).app c = ιS.hom.app (F.obj c) ≫ F.map (ιX.inv.app c) := by
  have h := unit_mateEquiv_symm adjX adjS α c
  simp only [Functor.id_obj] at h
  apply (adjS.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← h,
    ← cancel_mono (κS.hom.app (F.obj (uX.obj c)))]
  have hn := κS.hom.naturality (ιS.hom.app (F.obj c) ≫ F.map (ιX.inv.app c))
  simp only [Functor.id_obj, Functor.id_map] at hn
  rw [Category.assoc, Category.assoc, hn, reassoc_of% (hS (F.obj c)), Iso.inv_hom_id_app_assoc,
    hα, ← F.map_comp, hX]

end CategoryTheory

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

lemma Adjunction.ofNatIsoRight_unit_app {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
    (c : C) : (adj.ofNatIsoRight iso).unit.app c = adj.unit.app c ≫ iso.hom.app (F.obj c) := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]

/-- For an adjunction `L ⊣ R` transported to `L ⊣ S` along `S ≅ R`, with `ι : L ≅ 𝟭` and the
conjugate identification `R ≅ 𝟭`, the unit followed by `S ≅ R ≅ 𝟭` is `ι⁻¹`. -/
lemma Adjunction.unit_ofNatIsoRight_conjugateIsoEquiv {L R S : C ⥤ C} (adj : L ⊣ R)
    (I : S ≅ R) (ι : L ≅ 𝟭 C) (c : C) :
    (adj.ofNatIsoRight I.symm).unit.app c ≫
        (I ≪≫ conjugateIsoEquiv adj Adjunction.id ι.symm).hom.app (L.obj c) = ι.inv.app c := by
  have h := unit_conjugateEquiv adj Adjunction.id ι.inv c
  simp only [Functor.id_obj, Adjunction.id_unit, NatTrans.id_app, Functor.id_map,
    Category.id_comp] at h
  rw [Adjunction.ofNatIsoRight_unit_app, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app_assoc, conjugateIsoEquiv_apply_hom, Iso.symm_hom, h]

end CategoryTheory

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- The abstract shape of the description of the compactly supported Frobenius as
`F φ ∘ Φ^♯`: the base change `Ex : F ⋙ u_s ⟶ u_X ⋙ F` of the identity square is the identity,
and the composition isomorphism `u_{Φ ≫ 𝟙} ≅ u_X ⋙ u_Φ` is the identity through `u_X ≅ 𝟭`. -/
lemma frobeniusSharp_aux {F G : C ⥤ D} {us : D ⥤ D} {uX uΦ uΦ' LΦ SΦ : C ⥤ C}
    (adjΦ : uΦ ⊣ LΦ) [IsIso adjΦ.unit] (IΦ : SΦ ≅ LΦ) (ιs : us ≅ 𝟭 D) (ιX : uX ≅ 𝟭 C)
    (Ex : F ⋙ us ⟶ uX ⋙ F) [IsIso Ex]
    (c : G ≅ SΦ ⋙ F) (cU : uΦ' ≅ uX ⋙ uΦ) (e₁ : uΦ' ≅ uΦ) (e : uΦ' ⋙ G ≅ uΦ ⋙ F)
    (K : C) (e₂ : G.obj (uΦ.obj K) ⟶ F.obj (uΦ.obj K))
    (hE : Ex.app K = ιs.hom.app (F.obj K) ≫ F.map (ιX.inv.app K))
    (hcU : cU.hom.app K ≫ uΦ.map (ιX.hom.app K) = e₁.hom.app K)
    (he : e.hom.app K = G.map (e₁.hom.app K) ≫ e₂) {L : C} (φ : uΦ.obj K ⟶ L) :
    ιs.inv.app (F.obj K) ≫
        (asIso Ex ≪≫ Functor.isoWhiskerLeft uX (Functor.leftUnitor F).symm ≪≫
          Functor.isoWhiskerLeft uX (Functor.isoWhiskerRight (asIso adjΦ.unit) F) ≪≫
          Functor.isoWhiskerLeft uX (Functor.associator uΦ LΦ F) ≪≫
          Functor.isoWhiskerLeft uX
            (Functor.isoWhiskerLeft uΦ (Functor.isoWhiskerRight IΦ.symm F)) ≪≫
          Functor.isoWhiskerLeft uX (Functor.isoWhiskerLeft uΦ c.symm) ≪≫
          (Functor.associator uX uΦ G).symm ≪≫ Functor.isoWhiskerRight cU.symm G ≪≫ e).hom.app K ≫
        F.map φ =
      F.map (adjΦ.unit.app K ≫ IΦ.inv.app (uΦ.obj K)) ≫ c.inv.app (uΦ.obj K) ≫ e₂ ≫ F.map φ := by
  have h1 : uΦ.map (ιX.inv.app K) ≫ cU.inv.app K = e₁.inv.app K := by
    rw [← cancel_epi (e₁.hom.app K), Iso.hom_inv_id_app, ← hcU, Category.assoc,
      ← uΦ.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app]
  have hu := adjΦ.unit.naturality (ιX.inv.app K)
  have hI := IΦ.inv.naturality (uΦ.map (ιX.inv.app K))
  have hc := c.inv.naturality (uΦ.map (ιX.inv.app K))
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hu hI hc
  simp only [Iso.trans_hom, NatTrans.comp_app, asIso_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.assoc]
  rw [hE, Category.assoc, Iso.inv_hom_id_app_assoc, ← F.map_comp_assoc, hu, F.map_comp_assoc,
    ← F.map_comp_assoc (LΦ.map _), hI, F.map_comp_assoc, reassoc_of% hc, he,
    ← G.map_comp_assoc (uΦ.map (ιX.inv.app K)), h1, Category.assoc, ← G.map_comp_assoc,
    Iso.inv_hom_id_app]
  simp

end CategoryTheory
