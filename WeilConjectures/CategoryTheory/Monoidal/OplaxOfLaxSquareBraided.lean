/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braidedness of an oplax monoidal structure obtained from a lax square

We keep the setting of `WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare`: a natural
transformation `δG : G(X ⊗ Y) ⟶ G X ⊗ G Y` of bifunctors, for a functor `G : D₁ ⥤ D₂`, which is
compatible, through a natural transformation `e : G ⋙ Q₁ ⟶ Q₂ ⋙ F`, with the comonoidal structure
of an oplax monoidal functor `F : K₁ ⥤ K₂` and the lax monoidal structures of `Q₁` and `Q₂`.

If all four categories are braided, `F` is compatible with the braidings, the lax structures of
`Q₁` and `Q₂` are compatible with the braidings, and every object of `D₁` is isomorphic to `Q₁ a`
for some `a` in a class `S` for which the relevant components of `μ Q₂` are isomorphisms, then
`δG` is compatible with the braidings
(`CategoryTheory.Functor.OplaxMonoidal.map_braiding_comp_app_app_of_lax_square`).

A monoidal functor whose comonoidal structure is compatible with the braidings is braided
(`CategoryTheory.Functor.Braided.ofMapBraidingCompδ`).
-/

@[expose] public section

namespace CategoryTheory.Functor

open Category MonoidalCategory LaxMonoidal OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D]

/-- A monoidal functor whose comonoidal structure `δ` is compatible with the braidings is
braided. Its underlying monoidal structure is the given one. -/
@[instance_reducible]
def Braided.ofMapBraidingCompδ (F : C ⥤ D) [F.Monoidal]
    (h : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) :
    F.Braided :=
  { ‹F.Monoidal› with
    braided X Y := by
      rw [← cancel_mono (δ F Y X), assoc, h, Monoidal.μ_δ_assoc, assoc, Monoidal.μ_δ, comp_id] }

end CategoryTheory.Functor

namespace CategoryTheory.Functor.OplaxMonoidal

open Category MonoidalCategory LaxMonoidal

variable {K₁ K₂ D₁ D₂ : Type*} [Category* K₁] [Category* K₂] [Category* D₁] [Category* D₂]
  [MonoidalCategory K₁] [MonoidalCategory K₂] [MonoidalCategory D₁] [MonoidalCategory D₂]
  [BraidedCategory K₁] [BraidedCategory K₂] [BraidedCategory D₁] [BraidedCategory D₂]
  {G : D₁ ⥤ D₂}
  (δG : (postcompose₂.obj G).obj (curriedTensor D₁) ⟶
    (((whiskeringLeft₂ D₂).obj G).obj G).obj (curriedTensor D₂))

/-- The compatibility of `δG` with the braidings holds for `X, Y` as soon as it holds for
objects `X', Y'` isomorphic to them. -/
lemma map_braiding_comp_app_app_of_iso {X Y X' Y' : D₁} (iX : X' ≅ X) (iY : Y' ≅ Y)
    (h : G.map (β_ X' Y').hom ≫ (δG.app Y').app X' =
      (δG.app X').app Y' ≫ (β_ (G.obj X') (G.obj Y')).hom) :
    G.map (β_ X Y).hom ≫ (δG.app Y).app X = (δG.app X).app Y ≫ (β_ (G.obj X) (G.obj Y)).hom := by
  rw [← cancel_epi (G.map (iX.hom ⊗ₘ iY.hom)), ← G.map_comp_assoc,
    BraidedCategory.braiding_naturality, G.map_comp_assoc, ← app_app_comp_tensorHom,
    reassoc_of% h, ← BraidedCategory.braiding_naturality, ← app_app_comp_tensorHom_assoc]

variable {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} [Q₁.LaxMonoidal] [Q₂.LaxMonoidal]
  {F : K₁ ⥤ K₂} [F.OplaxMonoidal] (e : ∀ a, G.obj (Q₁.obj a) ⟶ Q₂.obj (F.obj a))

/-- The compatibility of `δG` with the braidings holds for objects of the form `Q₁ a`, `Q₁ b`,
provided the relevant components of `e` and `μ Q₂` are isomorphisms. -/
lemma map_braiding_comp_app_app_of_lax_square_obj
    (he : ∀ ⦃a b : K₁⦄ (f : a ⟶ b), G.map (Q₁.map f) ≫ e b = e a ≫ Q₂.map (F.map f))
    (hδ : ∀ a b, (δG.app (Q₁.obj a)).app (Q₁.obj b) ≫ (e a ⊗ₘ e b) ≫
      μ Q₂ (F.obj a) (F.obj b) = G.map (μ Q₁ a b) ≫ e (a ⊗ b) ≫ Q₂.map (δ F a b))
    (hQ₁ : ∀ a b, (β_ (Q₁.obj a) (Q₁.obj b)).hom ≫ μ Q₁ b a = μ Q₁ a b ≫ Q₁.map (β_ a b).hom)
    (hQ₂ : ∀ a b, (β_ (Q₂.obj a) (Q₂.obj b)).hom ≫ μ Q₂ b a = μ Q₂ a b ≫ Q₂.map (β_ a b).hom)
    (hF : ∀ a b, δ F a b ≫ (β_ (F.obj a) (F.obj b)).hom = F.map (β_ a b).hom ≫ δ F b a)
    (a b : K₁) [IsIso (e a)] [IsIso (e b)] [IsIso (μ Q₂ (F.obj b) (F.obj a))] :
    G.map (β_ (Q₁.obj a) (Q₁.obj b)).hom ≫ (δG.app (Q₁.obj b)).app (Q₁.obj a) =
      (δG.app (Q₁.obj a)).app (Q₁.obj b) ≫ (β_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b))).hom := by
  rw [← cancel_mono ((e b ⊗ₘ e a) ≫ μ Q₂ (F.obj b) (F.obj a)), assoc, hδ, ← G.map_comp_assoc,
    hQ₁, G.map_comp_assoc, reassoc_of% (he (β_ a b).hom), ← Q₂.map_comp, ← hF, Q₂.map_comp, assoc,
    ← BraidedCategory.braiding_naturality_assoc, hQ₂, reassoc_of% hδ]

/-- If every object of `D₁` is isomorphic to `Q₁ a` for some `a` in a class `S` for which the
relevant components of `μ Q₂` are isomorphisms, then `δG` is compatible with the braidings. -/
lemma map_braiding_comp_app_app_of_lax_square
    (he : ∀ ⦃a b : K₁⦄ (f : a ⟶ b), G.map (Q₁.map f) ≫ e b = e a ≫ Q₂.map (F.map f))
    (hδ : ∀ a b, (δG.app (Q₁.obj a)).app (Q₁.obj b) ≫ (e a ⊗ₘ e b) ≫
      μ Q₂ (F.obj a) (F.obj b) = G.map (μ Q₁ a b) ≫ e (a ⊗ b) ≫ Q₂.map (δ F a b))
    (hQ₁ : ∀ a b, (β_ (Q₁.obj a) (Q₁.obj b)).hom ≫ μ Q₁ b a = μ Q₁ a b ≫ Q₁.map (β_ a b).hom)
    (hQ₂ : ∀ a b, (β_ (Q₂.obj a) (Q₂.obj b)).hom ≫ μ Q₂ b a = μ Q₂ a b ≫ Q₂.map (β_ a b).hom)
    (hF : ∀ a b, δ F a b ≫ (β_ (F.obj a) (F.obj b)).hom = F.map (β_ a b).hom ≫ δ F b a)
    [∀ a, IsIso (e a)] (S : ObjectProperty K₁)
    (hS : ∀ X : D₁, ∃ a, S a ∧ Nonempty (Q₁.obj a ≅ X))
    (hμ : ∀ (x : K₂) (b : K₁), S b → IsIso (μ Q₂ x (F.obj b))) (X Y : D₁) :
    G.map (β_ X Y).hom ≫ (δG.app Y).app X = (δG.app X).app Y ≫ (β_ (G.obj X) (G.obj Y)).hom := by
  obtain ⟨a, ha, ⟨iX⟩⟩ := hS X
  obtain ⟨b, -, ⟨iY⟩⟩ := hS Y
  have := hμ (F.obj b) a ha
  exact map_braiding_comp_app_app_of_iso δG iX iY
    (map_braiding_comp_app_app_of_lax_square_obj δG e he hδ hQ₁ hQ₂ hF a b)

end CategoryTheory.Functor.OplaxMonoidal
