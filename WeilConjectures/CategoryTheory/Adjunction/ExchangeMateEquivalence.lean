/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!
# The exchange morphism along equivalences

For adjunctions `Lf ⊣ Rf`, `Lf' ⊣ Rf'` and an isomorphism `θ : G ⋙ Lf' ≅ Lf ⋙ G'`, the exchange
morphism `Rf ⋙ G ⟶ G' ⋙ Rf'` (`CategoryTheory.Adjunction.exchangeRight`) is an isomorphism as
soon as `G` and `G'` are equivalences
(`CategoryTheory.Adjunction.isIso_exchangeRight_of_isEquivalence`): on morphisms out of `G Y`, it
is the composite of the bijections given by the full faithfulness of `G` and `G'`, the two
adjunctions and `θ`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'}
  (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G')

/-- On a morphism `G y` out of an object `G Y`, the component of the exchange morphism is the
transpose under `Lf' ⊣ Rf'` of `θ_Y ≫ G' (y^♭)`, for the transpose `y^♭ : Lf Y ⟶ K` of `y`. -/
lemma map_comp_exchangeRight_app {Y : B} {K : A} (y : Y ⟶ Rf.obj K) :
    G.map y ≫ (exchangeRight af af' θ).app K =
      af'.homEquiv _ _ (θ.hom.app Y ≫ G'.map ((af.homEquiv _ _).symm y)) := by
  rw [exchangeRight_app, Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]
  have hu := af'.unit.naturality (G.map y)
  have h := θ.hom.naturality y
  dsimp at hu h
  rw [reassoc_of% hu]
  congr 1
  rw [← Rf'.map_comp, ← Rf'.map_comp]
  congr 1
  rw [G'.map_comp, reassoc_of% h]

/-- **The exchange morphism along equivalences is an isomorphism.** -/
lemma isIso_exchangeRight_of_isEquivalence [G.IsEquivalence] [G'.IsEquivalence] :
    IsIso (exchangeRight af af' θ) := by
  have hG : G.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful G
  have hG' : G'.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful G'
  have (K : A) : IsIso ((exchangeRight af af' θ).app K) := by
    rw [isIso_iff_yoneda_map_bijective]
    intro T
    let Y := G.objPreimage T
    let e : G.obj Y ≅ T := G.objObjPreimageIso T
    let E : (G.obj Y ⟶ G.obj (Rf.obj K)) ≃ (G.obj Y ⟶ Rf'.obj (G'.obj K)) :=
      hG.homEquiv.symm.trans ((af.homEquiv _ _).symm.trans (hG'.homEquiv.trans
        ((Equiv.mk (fun h ↦ θ.hom.app Y ≫ h) (fun h ↦ θ.inv.app Y ≫ h) (fun h ↦ by simp)
            (fun h ↦ by simp) : ((Lf ⋙ G').obj Y ⟶ G'.obj K) ≃ ((G ⋙ Lf').obj Y ⟶ G'.obj K)).trans
          (af'.homEquiv _ _))))
    have hE (x : G.obj Y ⟶ G.obj (Rf.obj K)) : E x = x ≫ (exchangeRight af af' θ).app K := by
      obtain ⟨y, rfl⟩ := hG.map_surjective x
      simp only [E, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_symm_apply,
        Functor.FullyFaithful.preimage_map, Functor.FullyFaithful.homEquiv_apply, Equiv.coe_fn_mk]
      exact (map_comp_exchangeRight_app af af' θ y).symm
    have hT : (fun x : T ⟶ (Rf ⋙ G).obj K ↦ x ≫ (exchangeRight af af' θ).app K) =
        (fun x ↦ e.inv ≫ x) ∘ E ∘ (fun x ↦ e.hom ≫ x) := by
      funext x
      simp only [Function.comp_apply, hE, Category.assoc, Iso.inv_hom_id_assoc]
    have h₁ : Function.Bijective fun x : G.obj Y ⟶ (G' ⋙ Rf').obj K ↦
        (e.inv ≫ x : T ⟶ (G' ⋙ Rf').obj K) :=
      Function.bijective_iff_has_inverse.2 ⟨fun x ↦ e.hom ≫ x, fun x ↦ by simp, fun x ↦ by simp⟩
    have h₂ : Function.Bijective fun x : T ⟶ (Rf ⋙ G).obj K ↦ e.hom ≫ x :=
      Function.bijective_iff_has_inverse.2 ⟨fun x ↦ e.inv ≫ x, fun x ↦ by simp, fun x ↦ by simp⟩
    convert (h₁.comp E.bijective).comp h₂ using 1
    exact hT
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory.Adjunction
