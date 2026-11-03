/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Products.Basic

/-! # Unitor squares for a tensor comparison

Formal pasting lemmas: a functor `H` between monoidal categories with a natural map
`σ : H (X ⊗ Y) ⟶ H X ⊗ H Y` and a unit comparison `e : H 𝟙 ⟶ 𝟙` is compatible with the
unitors once this is checked on chosen representatives (`rightUnitor_square_of_models`,
`leftUnitor_square_of_models`), and the compatibility transports along isomorphisms.
Source: Stacks Project, Tag 0FPT (formal monoidal pasting).
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalUnitorSquare

variable {D D' : Type*} [Category* D] [Category* D'] [MonoidalCategory D]
  [MonoidalCategory D'] (H : D ⥤ D')
  (σ : ∀ X Y : D, H.obj (X ⊗ Y) ⟶ H.obj X ⊗ H.obj Y)

/-- Naturality of a tensor comparison `σ`. -/
def SigmaNatural : Prop :=
  ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y'),
    H.map (f ⊗ₘ g) ≫ σ X' Y' = σ X Y ≫ (H.map f ⊗ₘ H.map g)

/-- The right unitor square holds at `X` once it is computed on a model `T ≅ X ⊗ U` of the
unit object. -/
theorem rightUnitor_square_of_models (hσnat : SigmaNatural H σ)
    {X U : D} (uE : 𝟙_ D ≅ U) {T : D} (tE : T ≅ X ⊗ U)
    {Y V U' : D'} (εX : H.obj X ≅ Y) (εU : H.obj U ⟶ V) (cU : V ⟶ U') (uL : 𝟙_ D' ≅ U')
    {T' T'' Z : D'} (tL : T' ≅ Y ⊗ V) (tL' : T'' ≅ Y ⊗ U') (εT : H.obj T ⟶ Z)
    (s : Z ⟶ T') (m : T' ⟶ T'') (rE : T ⟶ X) (rL : T'' ⟶ Y) (rEC : Z ⟶ Y)
    (hσ : H.map tE.hom ≫ σ X U ≫ (εX.hom ⊗ₘ εU) = εT ≫ s ≫ tL.hom)
    (hrE : tE.hom ≫ (𝟙 X ⊗ₘ uE.inv) ≫ (ρ_ X).hom = rE)
    (hrL : tL'.hom ≫ (𝟙 Y ⊗ₘ uL.inv) ≫ (ρ_ Y).hom = rL)
    (hm : m ≫ tL'.hom = tL.hom ≫ (𝟙 Y ⊗ₘ cU))
    (hstrict : s ≫ m ≫ rL = rEC)
    (hε : H.map rE ≫ εX.hom = εT ≫ rEC) :
    σ X (𝟙_ D) ≫ (𝟙 (H.obj X) ⊗ₘ (H.map uE.hom ≫ εU ≫ cU ≫ uL.inv)) ≫
      (ρ_ (H.obj X)).hom = H.map (ρ_ X).hom := by
  rw [id_tensorHom] at hrE hrL hm
  have hk : (H.obj X ◁ (εU ≫ cU ≫ uL.inv)) ≫ (ρ_ (H.obj X)).hom =
      (εX.hom ⊗ₘ εU) ≫ (Y ◁ cU) ≫ (Y ◁ uL.inv) ≫ (ρ_ Y).hom ≫ εX.inv := by
    simp only [tensorHom_def, Category.assoc, ← whisker_exchange_assoc,
      rightUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id, whiskerLeft_comp]
  have hn := hσnat (𝟙 X) uE.hom
  simp only [H.map_id, id_tensorHom] at hn
  have hkey : H.map tE.hom ≫ σ X U ≫ (H.obj X ◁ (εU ≫ cU ≫ uL.inv)) ≫
      (ρ_ (H.obj X)).hom = H.map rE := by
    rw [hk]
    calc _ = (H.map tE.hom ≫ σ X U ≫ (εX.hom ⊗ₘ εU)) ≫ (Y ◁ cU) ≫ (Y ◁ uL.inv) ≫
          (ρ_ Y).hom ≫ εX.inv := by simp only [Category.assoc]
      _ = εT ≫ s ≫ (tL.hom ≫ (Y ◁ cU)) ≫ (Y ◁ uL.inv) ≫ (ρ_ Y).hom ≫ εX.inv := by
          rw [hσ]
          simp only [Category.assoc]
      _ = εT ≫ (s ≫ m ≫ rL) ≫ εX.inv := by
          rw [← hm, ← hrL]
          simp only [Category.assoc]
      _ = H.map rE := by
          rw [hstrict, ← Category.assoc, ← hε]
          simp
  have hρ : (ρ_ X).hom = (X ◁ uE.hom) ≫ tE.inv ≫ rE := by
    rw [← hrE]
    simp
  have hinv : H.map tE.inv ≫ H.map tE.hom = 𝟙 _ := by
    rw [← H.map_comp, Iso.inv_hom_id, H.map_id]
  rw [hρ, H.map_comp, H.map_comp, ← hkey, reassoc_of% hinv, reassoc_of% hn]
  simp

/-- The left unitor square holds at `X` once it is computed on a model `T ≅ U ⊗ X` of the
unit object. -/
theorem leftUnitor_square_of_models (hσnat : SigmaNatural H σ)
    {X U : D} (uE : 𝟙_ D ≅ U) {T : D} (tE : T ≅ U ⊗ X)
    {Y V U' : D'} (εX : H.obj X ≅ Y) (εU : H.obj U ⟶ V) (cU : V ⟶ U') (uL : 𝟙_ D' ≅ U')
    {T' T'' Z : D'} (tL : T' ≅ V ⊗ Y) (tL' : T'' ≅ U' ⊗ Y) (εT : H.obj T ⟶ Z)
    (s : Z ⟶ T') (m : T' ⟶ T'') (lE : T ⟶ X) (lL : T'' ⟶ Y) (lEC : Z ⟶ Y)
    (hσ : H.map tE.hom ≫ σ U X ≫ (εU ⊗ₘ εX.hom) = εT ≫ s ≫ tL.hom)
    (hlE : tE.hom ≫ (uE.inv ⊗ₘ 𝟙 X) ≫ (λ_ X).hom = lE)
    (hlL : tL'.hom ≫ (uL.inv ⊗ₘ 𝟙 Y) ≫ (λ_ Y).hom = lL)
    (hm : m ≫ tL'.hom = tL.hom ≫ (cU ⊗ₘ 𝟙 Y))
    (hstrict : s ≫ m ≫ lL = lEC)
    (hε : H.map lE ≫ εX.hom = εT ≫ lEC) :
    σ (𝟙_ D) X ≫ ((H.map uE.hom ≫ εU ≫ cU ≫ uL.inv) ⊗ₘ 𝟙 (H.obj X)) ≫
      (λ_ (H.obj X)).hom = H.map (λ_ X).hom := by
  rw [tensorHom_id] at hlE hlL hm
  have hk : ((εU ≫ cU ≫ uL.inv) ▷ H.obj X) ≫ (λ_ (H.obj X)).hom =
      (εU ⊗ₘ εX.hom) ≫ (cU ▷ Y) ≫ (uL.inv ▷ Y) ≫ (λ_ Y).hom ≫ εX.inv := by
    simp only [tensorHom_def', Category.assoc, whisker_exchange_assoc,
      leftUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id, comp_whiskerRight]
  have hn := hσnat uE.hom (𝟙 X)
  simp only [H.map_id, tensorHom_id] at hn
  have hkey : H.map tE.hom ≫ σ U X ≫ ((εU ≫ cU ≫ uL.inv) ▷ H.obj X) ≫
      (λ_ (H.obj X)).hom = H.map lE := by
    rw [hk]
    calc _ = (H.map tE.hom ≫ σ U X ≫ (εU ⊗ₘ εX.hom)) ≫ (cU ▷ Y) ≫ (uL.inv ▷ Y) ≫
          (λ_ Y).hom ≫ εX.inv := by simp only [Category.assoc]
      _ = εT ≫ s ≫ (tL.hom ≫ (cU ▷ Y)) ≫ (uL.inv ▷ Y) ≫ (λ_ Y).hom ≫ εX.inv := by
          rw [hσ]
          simp only [Category.assoc]
      _ = εT ≫ (s ≫ m ≫ lL) ≫ εX.inv := by
          rw [← hm, ← hlL]
          simp only [Category.assoc]
      _ = H.map lE := by
          rw [hstrict, ← Category.assoc, ← hε]
          simp
  have hlam : (λ_ X).hom = (uE.hom ▷ X) ≫ tE.inv ≫ lE := by
    rw [← hlE]
    simp
  have hinv : H.map tE.inv ≫ H.map tE.hom = 𝟙 _ := by
    rw [← H.map_comp, Iso.inv_hom_id, H.map_id]
  rw [hlam, H.map_comp, H.map_comp, ← hkey, reassoc_of% hinv, reassoc_of% hn]
  simp

/-- The right unitor square transports along isomorphisms. -/
theorem rightUnitor_square_of_iso (hσnat : SigmaNatural H σ)
    (e : H.obj (𝟙_ D) ⟶ 𝟙_ D') {A A' : D} (i : A' ≅ A)
    (h : σ A' (𝟙_ D) ≫ (𝟙 (H.obj A') ⊗ₘ e) ≫ (ρ_ (H.obj A')).hom =
      H.map (ρ_ A').hom) :
    σ A (𝟙_ D) ≫ (𝟙 (H.obj A) ⊗ₘ e) ≫ (ρ_ (H.obj A)).hom = H.map (ρ_ A).hom := by
  rw [← cancel_epi (H.map (i.hom ▷ 𝟙_ D))]
  have hR : H.map (i.hom ▷ 𝟙_ D) ≫ H.map (ρ_ A).hom = H.map (ρ_ A').hom ≫ H.map i.hom := by
    rw [← H.map_comp, ← H.map_comp, rightUnitor_naturality]
  have hn := hσnat i.hom (𝟙 (𝟙_ D))
  simp only [H.map_id, tensorHom_id] at hn
  rw [hR, ← h, reassoc_of% hn]
  simp only [id_tensorHom, Category.assoc]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]

/-- The left unitor square transports along isomorphisms. -/
theorem leftUnitor_square_of_iso (hσnat : SigmaNatural H σ)
    (e : H.obj (𝟙_ D) ⟶ 𝟙_ D') {A A' : D} (i : A' ≅ A)
    (h : σ (𝟙_ D) A' ≫ (e ⊗ₘ 𝟙 (H.obj A')) ≫ (λ_ (H.obj A')).hom =
      H.map (λ_ A').hom) :
    σ (𝟙_ D) A ≫ (e ⊗ₘ 𝟙 (H.obj A)) ≫ (λ_ (H.obj A)).hom = H.map (λ_ A).hom := by
  rw [← cancel_epi (H.map (𝟙_ D ◁ i.hom))]
  have hL : H.map (𝟙_ D ◁ i.hom) ≫ H.map (λ_ A).hom = H.map (λ_ A').hom ≫ H.map i.hom := by
    rw [← H.map_comp, ← H.map_comp, leftUnitor_naturality]
  have hn := hσnat (𝟙 (𝟙_ D)) i.hom
  simp only [H.map_id, id_tensorHom] at hn
  rw [hL, ← h, reassoc_of% hn]
  simp only [tensorHom_id, Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality]

end CategoryTheory.MonoidalUnitorSquare
