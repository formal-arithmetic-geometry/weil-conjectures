/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-!
# Composites of comparisons induced through lax monoidal functors

Consider three squares as in `WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare`
```
  H₁ ──F₁₂──▶ H₂ ──F₂₃──▶ H₃          H₁ ──F₁₃──▶ H₃
  │           │           │           │           │
  Q₁          Q₂          Q₃          Q₁          Q₃
  ▼           ▼           ▼           ▼           ▼
  D₁ ──G₁₂──▶ D₂ ──G₂₃──▶ D₃          D₁ ──G₁₃──▶ D₃
```
with counits `c : Q ⋙ G ⟶ F ⋙ Q`, and comparisons `δ : G(X ⊗ Y) ⟶ G X ⊗ G Y` induced by the
comonoidal structures of the functors `F` through the counits. An isomorphism
`e : G₁₃ ≅ G₁₂ ⋙ G₂₃` which is induced, through the counits, by maps `F₁₃ a ⟶ F₂₃ (F₁₂ a)`
compatible with the comonoidal structures, is compatible with the comparisons `δ` on objects
`Q₁ a ⊗ Q₁ b` (`CategoryTheory.Functor.OplaxMonoidal.comp_app_app_comp_of_lax_square`).
Compatibility at `X, Y` follows from compatibility at objects isomorphic to them
(`CategoryTheory.Functor.OplaxMonoidal.comp_app_app_of_iso`).

The typical example is the composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` of derived
pullbacks.
-/

@[expose] public section

namespace CategoryTheory.Functor.OplaxMonoidal

open Category MonoidalCategory LaxMonoidal

variable {H₁ H₂ H₃ D₁ D₂ D₃ : Type*} [Category* H₁] [Category* H₂] [Category* H₃]
  [Category* D₁] [Category* D₂] [Category* D₃] [MonoidalCategory H₁] [MonoidalCategory H₂]
  [MonoidalCategory H₃] [MonoidalCategory D₁] [MonoidalCategory D₂] [MonoidalCategory D₃]
  {Q₁ : H₁ ⥤ D₁} {Q₂ : H₂ ⥤ D₂} {Q₃ : H₃ ⥤ D₃} [Q₁.LaxMonoidal] [Q₂.LaxMonoidal] [Q₃.LaxMonoidal]
  {F₁₂ : H₁ ⥤ H₂} {F₂₃ : H₂ ⥤ H₃} {F₁₃ : H₁ ⥤ H₃} [F₁₂.OplaxMonoidal] [F₂₃.OplaxMonoidal]
  [F₁₃.OplaxMonoidal] {G₁₂ : D₁ ⥤ D₂} {G₂₃ : D₂ ⥤ D₃} {G₁₃ : D₁ ⥤ D₃}
  {δ₁₂ : (postcompose₂.obj G₁₂).obj (curriedTensor D₁) ⟶
    (((whiskeringLeft₂ D₂).obj G₁₂).obj G₁₂).obj (curriedTensor D₂)}
  {δ₂₃ : (postcompose₂.obj G₂₃).obj (curriedTensor D₂) ⟶
    (((whiskeringLeft₂ D₃).obj G₂₃).obj G₂₃).obj (curriedTensor D₃)}
  {δ₁₃ : (postcompose₂.obj G₁₃).obj (curriedTensor D₁) ⟶
    (((whiskeringLeft₂ D₃).obj G₁₃).obj G₁₃).obj (curriedTensor D₃)}
  {c₁₂ : Q₁ ⋙ G₁₂ ⟶ F₁₂ ⋙ Q₂} {c₂₃ : Q₂ ⋙ G₂₃ ⟶ F₂₃ ⋙ Q₃} {c₁₃ : Q₁ ⋙ G₁₃ ⟶ F₁₃ ⋙ Q₃}
  (e : G₁₃ ≅ G₁₂ ⋙ G₂₃) (s : ∀ a, F₁₃.obj a ⟶ F₂₃.obj (F₁₂.obj a))
  (s' : ∀ a, F₂₃.obj (F₁₂.obj a) ⟶ F₁₃.obj a)

/-- **Composites of induced comparisons.** If `e : G₁₃ ≅ G₁₂ ⋙ G₂₃` is induced through the
counits by maps `s a : F₁₃ a ⟶ F₂₃ (F₁₂ a)` with left inverses `s' a`, compatible with the
comonoidal structures, then on objects `Q₁ a ⊗ Q₁ b` the composite
`e ≫ G₂₃(δ₁₂) ≫ δ₂₃ ≫ (e⁻¹ ⊗ e⁻¹)` agrees with `δ₁₃` after the counit `(c₁₃ ⊗ c₁₃) ≫ μ Q₃`. -/
lemma comp_app_app_comp_of_lax_square
    (h₁₂ : ∀ a b, (δ₁₂.app (Q₁.obj a)).app (Q₁.obj b) ≫ (c₁₂.app a ⊗ₘ c₁₂.app b) ≫
      μ Q₂ _ _ = G₁₂.map (μ Q₁ a b) ≫ c₁₂.app (a ⊗ b) ≫ Q₂.map (δ F₁₂ a b))
    (h₂₃ : ∀ a b, (δ₂₃.app (Q₂.obj a)).app (Q₂.obj b) ≫ (c₂₃.app a ⊗ₘ c₂₃.app b) ≫
      μ Q₃ _ _ = G₂₃.map (μ Q₂ a b) ≫ c₂₃.app (a ⊗ b) ≫ Q₃.map (δ F₂₃ a b))
    (h₁₃ : ∀ a b, (δ₁₃.app (Q₁.obj a)).app (Q₁.obj b) ≫ (c₁₃.app a ⊗ₘ c₁₃.app b) ≫
      μ Q₃ _ _ = G₁₃.map (μ Q₁ a b) ≫ c₁₃.app (a ⊗ b) ≫ Q₃.map (δ F₁₃ a b))
    (hss' : ∀ a, s a ≫ s' a = 𝟙 _)
    (he : ∀ a, e.hom.app (Q₁.obj a) ≫ G₂₃.map (c₁₂.app a) ≫ c₂₃.app (F₁₂.obj a) =
      c₁₃.app a ≫ Q₃.map (s a))
    (hs : ∀ a b, s (a ⊗ b) ≫ F₂₃.map (δ F₁₂ a b) ≫ δ F₂₃ _ _ = δ F₁₃ a b ≫ (s a ⊗ₘ s b))
    (a b : H₁) :
    (e.hom.app (Q₁.obj a ⊗ Q₁.obj b) ≫ G₂₃.map ((δ₁₂.app (Q₁.obj a)).app (Q₁.obj b)) ≫
        (δ₂₃.app (G₁₂.obj (Q₁.obj a))).app (G₁₂.obj (Q₁.obj b))) ≫
      (e.inv.app (Q₁.obj a) ⊗ₘ e.inv.app (Q₁.obj b)) ≫ (c₁₃.app a ⊗ₘ c₁₃.app b) ≫
        μ Q₃ _ _ =
      (δ₁₃.app (Q₁.obj a)).app (Q₁.obj b) ≫ (c₁₃.app a ⊗ₘ c₁₃.app b) ≫ μ Q₃ _ _ := by
  have hE (x : H₁) : e.inv.app (Q₁.obj x) ≫ c₁₃.app x =
      G₂₃.map (c₁₂.app x) ≫ c₂₃.app (F₁₂.obj x) ≫ Q₃.map (s' x) := by
    rw [← cancel_epi (e.hom.app (Q₁.obj x)), Iso.hom_inv_id_app_assoc, reassoc_of% (he x),
      ← Q₃.map_comp, hss', Q₃.map_id, comp_id]
  have hc₂₃ {x y : H₂} (f : x ⟶ y) : G₂₃.map (Q₂.map f) ≫ c₂₃.app y =
      c₂₃.app x ≫ Q₃.map (F₂₃.map f) := c₂₃.naturality f
  have hen {x y : D₁} (f : x ⟶ y) : e.hom.app x ≫ G₂₃.map (G₁₂.map f) =
      G₁₃.map f ≫ e.hom.app y := (e.hom.naturality f).symm
  rw [tensorHom_comp_tensorHom_assoc, hE, hE, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom]
  simp only [assoc]
  rw [OplaxMonoidal.app_app_comp_tensorHom_assoc δ₂₃, μ_natural]
  erw [reassoc_of% (h₂₃ _ _)]
  rw [
    ← G₂₃.map_comp_assoc, ← G₂₃.map_comp_assoc, assoc, h₁₂, G₂₃.map_comp, G₂₃.map_comp, assoc,
    assoc, reassoc_of% (hc₂₃ _), reassoc_of% (hen _), reassoc_of% (he _), h₁₃]
  simp only [← Q₃.map_comp]
  rw [reassoc_of% (hs a b), tensorHom_comp_tensorHom, hss', hss', tensorHom_id, id_whiskerRight,
    comp_id]


omit [MonoidalCategory H₁] [MonoidalCategory H₂] [MonoidalCategory H₃] [Q₁.LaxMonoidal]
  [Q₂.LaxMonoidal] [Q₃.LaxMonoidal] [F₁₂.OplaxMonoidal] [F₂₃.OplaxMonoidal]
  [F₁₃.OplaxMonoidal] in
/-- The compatibility of `e : G₁₃ ≅ G₁₂ ⋙ G₂₃` with comparisons `δ` holds at `X, Y` as soon as
it holds at objects isomorphic to them. -/
lemma comp_app_app_of_iso {X Y X' Y' : D₁} (iX : X' ≅ X) (iY : Y' ≅ Y)
    (h : e.hom.app (X' ⊗ Y') ≫ G₂₃.map ((δ₁₂.app X').app Y') ≫
        (δ₂₃.app (G₁₂.obj X')).app (G₁₂.obj Y') =
      (δ₁₃.app X').app Y' ≫ (e.hom.app X' ⊗ₘ e.hom.app Y')) :
    e.hom.app (X ⊗ Y) ≫ G₂₃.map ((δ₁₂.app X).app Y) ≫
        (δ₂₃.app (G₁₂.obj X)).app (G₁₂.obj Y) =
      (δ₁₃.app X).app Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) := by
  rw [← cancel_epi (G₁₃.map (iX.hom ⊗ₘ iY.hom))]
  have h₁ := e.hom.naturality (iX.hom ⊗ₘ iY.hom)
  dsimp only [Functor.comp_map] at h₁
  rw [reassoc_of% h₁, ← G₂₃.map_comp_assoc, ← app_app_comp_tensorHom, G₂₃.map_comp_assoc,
    ← app_app_comp_tensorHom, reassoc_of% h, ← app_app_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp only [Functor.comp_map, e.hom.naturality]

omit [MonoidalCategory H₁] [MonoidalCategory H₂] [MonoidalCategory H₃] [Q₁.LaxMonoidal]
  [Q₂.LaxMonoidal] [Q₃.LaxMonoidal] [F₁₂.OplaxMonoidal] [F₂₃.OplaxMonoidal]
  [F₁₃.OplaxMonoidal] in
/-- The compatibility of `e : G₁₃ ≅ G₁₂ ⋙ G₂₃` with comparisons `δ` at `X, Y`, from its
composite with a monomorphism `m` and the inverse of `e`. -/
lemma comp_app_app_of_mono {X Y : D₁} {Z : D₃} (m : G₁₃.obj X ⊗ G₁₃.obj Y ⟶ Z) [Mono m]
    (h : (e.hom.app (X ⊗ Y) ≫ G₂₃.map ((δ₁₂.app X).app Y) ≫
        (δ₂₃.app (G₁₂.obj X)).app (G₁₂.obj Y)) ≫ (e.inv.app X ⊗ₘ e.inv.app Y) ≫ m =
      (δ₁₃.app X).app Y ≫ m) :
    e.hom.app (X ⊗ Y) ≫ G₂₃.map ((δ₁₂.app X).app Y) ≫
        (δ₂₃.app (G₁₂.obj X)).app (G₁₂.obj Y) =
      (δ₁₃.app X).app Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) := by
  rw [← cancel_mono ((e.inv.app X ⊗ₘ e.inv.app Y) ≫ m), h, assoc, tensorHom_comp_tensorHom_assoc,
    Iso.hom_inv_id_app, Iso.hom_inv_id_app, tensorHom_id, id_whiskerRight, id_comp]

end CategoryTheory.Functor.OplaxMonoidal
