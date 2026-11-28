/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Left mates under restriction to full subcategories

For adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and a square `β : R₁ ⋙ G ⟶ H ⋙ R₂`, the left mate
`(mateEquiv adj₁ adj₂).symm β : G ⋙ L₂ ⟶ L₁ ⋙ H` is computed componentwise
(`CategoryTheory.mateEquiv_symm_app`).

* `CategoryTheory.map_mateEquiv_symm_restrictFullyFaithful_app`: the left mate of the
  restrictions of adjunctions to full subcategories
  (`CategoryTheory.Adjunction.restrictFullyFaithful`) is the left mate of the ambient
  adjunctions, for compatible squares; in particular it is invertible as soon as the ambient one
  is (`CategoryTheory.isIso_mateEquiv_symm_restrictFullyFaithful`,
  `CategoryTheory.isIso_mateEquiv_symm_restrictFullyFaithful_lift`).

## Implementation details

In `CategoryTheory.isIso_mateEquiv_symm_restrictFullyFaithful_lift`, the category structures are
implicit arguments determined by unification rather than instance arguments: the lemma is
applied to functors whose category structures were elaborated in other files, and synthesizing
them again can produce different terms, which the kernel then has to compare by unfolding.
-/

@[expose] public section

namespace CategoryTheory

open Category Adjunction

section MateApp

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The component of the left mate of a square: the unit of `L₁ ⊣ R₁`, then the square, then the
counit of `L₂ ⊣ R₂`. -/
lemma mateEquiv_symm_app (β : TwoSquare R₁ H G R₂) (X : A) :
    ((mateEquiv adj₁ adj₂).symm β).app X =
      L₂.map (G.map (adj₁.unit.app X)) ≫ L₂.map (β.app (L₁.obj X)) ≫
        adj₂.counit.app (H.obj (L₁.obj X)) := by
  simp

end MateApp

section Restrict

variable {C D C' D' Ca Da Ca' Da' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Category* Ca] [Category* Da] [Category* Ca'] [Category* Da']
  {iC : C ⥤ Ca} {iD : D ⥤ Da} {iC' : C' ⥤ Ca'} {iD' : D' ⥤ Da'}
  (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful) (hiC' : iC'.FullyFaithful)
  (hiD' : iD'.FullyFaithful)
  {La : Ca ⥤ Da} {Ra : Da ⥤ Ca} {La' : Ca' ⥤ Da'} {Ra' : Da' ⥤ Ca'}
  (adja : La ⊣ Ra) (adja' : La' ⊣ Ra')
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  (comm1 : iC ⋙ La ≅ L ⋙ iD) (comm2 : iD ⋙ Ra ≅ R ⋙ iC)
  (comm1' : iC' ⋙ La' ≅ L' ⋙ iD') (comm2' : iD' ⋙ Ra' ≅ R' ⋙ iC')
  {G : C ⥤ C'} {H : D ⥤ D'} {Ga : Ca ⥤ Ca'} {Ha : Da ⥤ Da'}
  (eG : G ⋙ iC' ≅ iC ⋙ Ga) (eH : H ⋙ iD' ≅ iD ⋙ Ha)

/-- The left mate of the restrictions of adjunctions to full subcategories is, after the
inclusion, the left mate of the ambient adjunctions, for squares compatible through the
inclusions. -/
lemma map_mateEquiv_symm_restrictFullyFaithful_app (β : TwoSquare R H G R')
    (βa : TwoSquare Ra Ha Ga Ra')
    (hβ : ∀ d, iC'.map (β.app d) = eG.hom.app (R.obj d) ≫ Ga.map (comm2.inv.app d) ≫
      βa.app (iD.obj d) ≫ Ra'.map (eH.inv.app d) ≫ comm2'.hom.app (H.obj d)) (c : C) :
    iD'.map (((mateEquiv (adja.restrictFullyFaithful hiC hiD comm1 comm2)
      (adja'.restrictFullyFaithful hiC' hiD' comm1' comm2')).symm β).app c) =
      comm1'.inv.app (G.obj c) ≫ La'.map (eG.hom.app c) ≫
        ((mateEquiv adja adja').symm βa).app (iC.obj c) ≫ Ha.map (comm1.hom.app c) ≫
        eH.inv.app (L.obj c) := by
  have hL : ∀ {x y : C'} (f : x ⟶ y), iD'.map (L'.map f) =
      comm1'.inv.app x ≫ La'.map (iC'.map f) ≫ comm1'.hom.app y := fun f ↦
    (NatIso.naturality_1 comm1' f).symm
  have hG : ∀ {x y : C} (f : x ⟶ y), iC'.map (G.map f) =
      eG.hom.app x ≫ Ga.map (iC.map f) ≫ eG.inv.app y := fun f ↦
    (NatIso.naturality_2 eG f).symm
  rw [mateEquiv_symm_app, mateEquiv_symm_app, Functor.map_comp, Functor.map_comp, hL, hL,
    map_restrictFullyFaithful_counit_app, hG, hβ, map_restrictFullyFaithful_unit_app]
  simp only [Functor.map_comp, assoc, Iso.hom_inv_id_app_assoc]
  erw [Iso.hom_inv_id_app_assoc]
  simp only [← La'.map_comp_assoc, Iso.hom_inv_id_app, ← Ga.map_comp_assoc]
  congr 1
  have h₁ := adja'.counit.naturality (Ha.map (comm1.hom.app c) ≫ eH.inv.app (L.obj c))
  have h₂ := βa.naturality (comm1.hom.app c)
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at h₁ h₂
  rw [← h₁, ← La'.map_comp_assoc]
  congr 2
  erw [Iso.inv_hom_id_app_assoc]
  simp only [← Ga.map_comp_assoc, assoc, Iso.hom_inv_id_app]
  erw [comp_id, comp_id]
  rw [Ga.map_comp, assoc, reassoc_of% h₂, Ra'.map_comp]
  rfl


/-- The left mate of the restrictions of adjunctions to full subcategories is invertible as soon
as the left mate of the ambient adjunctions is, for squares compatible through the
inclusions. -/
lemma isIso_mateEquiv_symm_restrictFullyFaithful (β : TwoSquare R H G R')
    (βa : TwoSquare Ra Ha Ga Ra') [IsIso ((mateEquiv adja adja').symm βa)]
    (hβ : ∀ d, iC'.map (β.app d) = eG.hom.app (R.obj d) ≫ Ga.map (comm2.inv.app d) ≫
      βa.app (iD.obj d) ≫ Ra'.map (eH.inv.app d) ≫ comm2'.hom.app (H.obj d)) :
    IsIso ((mateEquiv (adja.restrictFullyFaithful hiC hiD comm1 comm2)
      (adja'.restrictFullyFaithful hiC' hiD' comm1' comm2')).symm β) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  have := hiD'.full
  have := hiD'.faithful
  have : IsIso (iD'.map (((mateEquiv (adja.restrictFullyFaithful hiC hiD comm1 comm2)
      (adja'.restrictFullyFaithful hiC' hiD' comm1' comm2')).symm β).app c)) := by
    rw [map_mateEquiv_symm_restrictFullyFaithful_app hiC hiD hiC' hiD' adja adja' comm1 comm2
      comm1' comm2' eG eH β βa hβ]
    infer_instance
  exact isIso_of_fully_faithful iD' _

end Restrict

section Lift

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄} {_ : Category.{v₁} C}
  {_ : Category.{v₂} D} {_ : Category.{v₃} C'} {_ : Category.{v₄} D'}
  {PC : ObjectProperty C} {PD : ObjectProperty D} {PC' : ObjectProperty C'}
  {PD' : ObjectProperty D'}
  {La : C ⥤ D} {Ra : D ⥤ C} {La' : C' ⥤ D'} {Ra' : D' ⥤ C'}
  (adja : La ⊣ Ra) (adja' : La' ⊣ Ra') {Ga : C ⥤ C'} {Ha : D ⥤ D'}
  (hLa : ∀ X, PC X → PD (La.obj X)) (hRa : ∀ Y, PD Y → PC (Ra.obj Y))
  (hLa' : ∀ X, PC' X → PD' (La'.obj X)) (hRa' : ∀ Y, PD' Y → PC' (Ra'.obj Y))
  (hGa : ∀ X, PC X → PC' (Ga.obj X)) (hHa : ∀ Y, PD Y → PD' (Ha.obj Y))

/-- The left mate of the restrictions of adjunctions to full subcategories stable under all the
functors involved is invertible as soon as the ambient left mate is, for a square lifting the
ambient one. -/
lemma isIso_mateEquiv_symm_restrictFullyFaithful_lift
    (β : TwoSquare (PC.lift (PD.ι ⋙ Ra) fun Y ↦ hRa _ Y.2)
      (PD'.lift (PD.ι ⋙ Ha) fun Y ↦ hHa _ Y.2) (PC'.lift (PC.ι ⋙ Ga) fun X ↦ hGa _ X.2)
      (PC'.lift (PD'.ι ⋙ Ra') fun Y ↦ hRa' _ Y.2))
    (βa : TwoSquare Ra Ha Ga Ra') [IsIso ((mateEquiv adja adja').symm βa)]
    (hβ : ∀ d, (β.app d).hom = βa.app d.obj) :
    IsIso ((mateEquiv
      (adja.restrictFullyFaithful PC.fullyFaithfulι PD.fullyFaithfulι
        (PD.liftCompιIso (PC.ι ⋙ La) fun X ↦ hLa _ X.2).symm
        (PC.liftCompιIso (PD.ι ⋙ Ra) fun Y ↦ hRa _ Y.2).symm)
      (adja'.restrictFullyFaithful PC'.fullyFaithfulι PD'.fullyFaithfulι
        (PD'.liftCompιIso (PC'.ι ⋙ La') fun X ↦ hLa' _ X.2).symm
        (PC'.liftCompιIso (PD'.ι ⋙ Ra') fun Y ↦ hRa' _ Y.2).symm)).symm β) :=
  isIso_mateEquiv_symm_restrictFullyFaithful _ _ _ _ adja adja' _ _ _ _
    (PC'.liftCompιIso _ _) (PD'.liftCompιIso _ _) β βa fun d ↦ by
      simp [ObjectProperty.liftCompιIso, hβ]

end Lift

end CategoryTheory
