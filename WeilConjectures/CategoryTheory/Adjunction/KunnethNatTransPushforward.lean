/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethNatTrans

/-!

# Künneth maps and pushforwards

Consider a square of adjunctions between monoidal categories
```
D' ──F'──▶ C'
▲ A        ▲ A'
D  ──F───▶ C
```
with left adjoints `F ⊣ G`, `F' ⊣ G'`, `A ⊣ H`, `A' ⊣ H'` oplax monoidal, and a monoidal
isomorphism `θ : F ⋙ A' ≅ A ⋙ F'`. In the application to the six functors, `F` and `F'` are the
pullbacks along `𝟙 × j : X ⨯ U ⟶ X ⨯ Y` and `𝟙 × j : Z ⨯ U ⟶ Z ⨯ Y`, and `A`, `A'` are the
pullbacks along `g × 𝟙` for a closed immersion `g : Z ⟶ X`.

The Künneth map `H P' ⊗ C₀ ⟶ G (H' Q' ⊗ D₀)` (the transpose of
`F (H P' ⊗ C₀) ⟶ F H P' ⊗ F C₀ ⟶ H' Q' ⊗ D₀`) is identified, through the projection morphisms of
`A ⊣ H` and `A' ⊣ H'` and the conjugate `H G' ⟶ G H'` of `θ`, with `H` applied to the Künneth map
`P' ⊗ C₀' ⟶ G' (Q' ⊗ D₀')`
(`CategoryTheory.Adjunction.homEquiv_δ_tensorHom_comp_map_projectionMorphism`).
Consequently, if the counits of `A ⊣ H` and `A' ⊣ H'` are isomorphisms (closed immersions) and
the projection morphisms are isomorphisms (projection formula), the Künneth map at an object
isomorphic to a pushforward is an isomorphism as soon as the Künneth map upstairs is
(`CategoryTheory.Adjunction.isIso_kunnethNatTrans_app_of_pushforward`).

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

section Naturality

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The transpose of `F (P ⊗ C₀) ⟶ F P ⊗ F C₀ ⟶ Q ⊗ D₀` is natural in `Q`. -/
lemma homEquiv_δ_tensorHom_comp_right {P C₀ : D} {Q Q₁ D₀ : C} (ε : F.obj P ⟶ Q)
    (v : Q ⟶ Q₁) (c : F.obj C₀ ⟶ D₀) :
    adj.homEquiv _ _ (δ F P C₀ ≫ ((ε ≫ v) ⊗ₘ c)) =
      adj.homEquiv _ _ (δ F P C₀ ≫ (ε ⊗ₘ c)) ≫ G.map (v ▷ D₀) := by
  rw [← homEquiv_naturality_right, Category.assoc, tensorHom_comp_whiskerRight]

/-- The transpose of `F (P ⊗ C₀) ⟶ F P ⊗ F C₀ ⟶ Q ⊗ D₀` is natural in `P`. -/
lemma homEquiv_δ_tensorHom_map_comp {P P₁ C₀ : D} {Q D₀ : C} (u : P₁ ⟶ P) (ε : F.obj P ⟶ Q)
    (c : F.obj C₀ ⟶ D₀) :
    adj.homEquiv _ _ (δ F P₁ C₀ ≫ ((F.map u ≫ ε) ⊗ₘ c)) =
      u ▷ C₀ ≫ adj.homEquiv _ _ (δ F P C₀ ≫ (ε ⊗ₘ c)) := by
  rw [← homEquiv_naturality_left, ← δ_natural_left_assoc, whiskerRight_comp_tensorHom]

end Naturality

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {C' : Type u₃} [Category.{v₃} C'] [MonoidalCategory C']
  {D' : Type u₄} [Category.{v₄} D'] [MonoidalCategory D']
  {F : D ⥤ C} {G : C ⥤ D} (adjF : F ⊣ G) {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adjF' : F' ⊣ G')
  {A : D ⥤ D'} {H : D' ⥤ D} (adjA : A ⊣ H) {A' : C ⥤ C'} {H' : C' ⥤ C} (adjA' : A' ⊣ H')
  [F.OplaxMonoidal] [F'.OplaxMonoidal] [A.OplaxMonoidal] [A'.OplaxMonoidal]
  (θ : F ⋙ A' ≅ A ⋙ F')

/-- **The Künneth map of a pushforward.** For a monoidal isomorphism `θ : F ⋙ A' ≅ A ⋙ F'`,
morphisms `ε : F H P' ⟶ H' Q'`, `c : F C₀ ⟶ D₀` and `ε' : F' P' ⟶ Q'`, `c' : F' C₀' ⟶ D₀'`
compatible through `θ`, the counits of `A ⊣ H`, `A' ⊣ H'` and morphisms `φ : A C₀ ⟶ C₀'`,
`ψ : D₀' ⟶ A' D₀`, the square
```
H P' ⊗ C₀ ────────────Künneth────────────▶ G (H' Q' ⊗ D₀)
   │ projection morphism                      │ G (projection morphism)
   ▼                                          ▼
H (P' ⊗ A C₀) ⟶ H (P' ⊗ C₀') ──H Künneth──▶ H G' (Q' ⊗ D₀') ⟶ G H' (Q' ⊗ D₀') ⟶ G H' (Q' ⊗ A' D₀)
```
commutes, where `H G' ⟶ G H'` is the conjugate of `θ`. -/
lemma homEquiv_δ_tensorHom_comp_map_projectionMorphism
    (hθ : ∀ X Y : D, θ.hom.app (X ⊗ Y) ≫ F'.map (δ A X Y) ≫ δ F' (A.obj X) (A.obj Y) =
      A'.map (δ F X Y) ≫ δ A' (F.obj X) (F.obj Y) ≫ (θ.hom.app X ⊗ₘ θ.hom.app Y))
    {P' : D'} {Q' : C'} {C₀ : D} {D₀ : C} {C₀' : D'} {D₀' : C'}
    (ε : F.obj (H.obj P') ⟶ H'.obj Q') (c : F.obj C₀ ⟶ D₀) (ε' : F'.obj P' ⟶ Q')
    (c' : F'.obj C₀' ⟶ D₀') (φ : A.obj C₀ ⟶ C₀') (ψ : D₀' ⟶ A'.obj D₀)
    (hε : θ.hom.app (H.obj P') ≫ F'.map (adjA.counit.app P') ≫ ε' =
      A'.map ε ≫ adjA'.counit.app Q')
    (hc : θ.hom.app C₀ ≫ F'.map φ ≫ c' ≫ ψ = A'.map c) :
    adjF.homEquiv _ _ (δ F (H.obj P') C₀ ≫ (ε ⊗ₘ c)) ≫
        G.map (adjA'.projectionMorphism Q' D₀) =
      adjA.projectionMorphism P' C₀ ≫
        H.map (P' ◁ φ ≫ adjF'.homEquiv _ _ (δ F' P' C₀' ≫ (ε' ⊗ₘ c'))) ≫
        (conjugateEquiv (adjA.comp adjF') (adjF.comp adjA') θ.hom).app _ ≫
        G.map (H'.map (Q' ◁ ψ)) := by
  apply ((adjF.comp adjA').homEquiv _ _).symm.injective
  have hτ {X : D} {W : C'} (x : X ⟶ H.obj (G'.obj W)) :
      ((adjF.comp adjA').homEquiv _ _).symm
          (x ≫ (conjugateEquiv (adjA.comp adjF') (adjF.comp adjA') θ.hom).app W) =
        θ.hom.app X ≫ ((adjA.comp adjF').homEquiv _ _).symm x := by
    rw [homEquiv_counit, homEquiv_counit, Functor.map_comp, Category.assoc,
      conjugateEquiv_counit, ← θ.hom.naturality_assoc]
  rw [← Category.assoc _ _ (G.map (H'.map _)), ← Category.assoc _ _ (G.map (H'.map _))]
  erw [homEquiv_naturality_right_symm]
  rw [← Category.assoc (adjA.projectionMorphism P' C₀), hτ]
  simp only [comp_homEquiv, Equiv.symm_trans_apply, projectionMorphism]
  erw [homEquiv_naturality_right_symm, Equiv.symm_apply_apply, homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply, homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
    homEquiv_naturality_left_symm]
  rw [homEquiv_naturality_left_symm, Equiv.symm_apply_apply, Functor.map_comp, Category.assoc,
    ← δ_natural_assoc, tensorHom_comp_whiskerRight, ← hε, ← hc]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc F' _ (P' ◁ φ), Category.assoc]
  erw [← tensorHom_def (adjA.counit.app P') φ]
  rw [Functor.map_comp_assoc]
  erw [← δ_natural_assoc]
  erw [reassoc_of% hθ]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_whiskerLeft]
  erw [tensorHom_comp_tensorHom]
  simp only [Category.assoc]

/-- **Künneth maps at pushforwards.** Let `θ : F ⋙ A' ≅ A ⋙ F'` be a monoidal isomorphism, and
suppose that `P M ≅ H (P' N)` and `Q M ≅ H' (Q' N)`, that the counits of `A ⊣ H` at `P' N` and of
`A' ⊣ H'` at `Q' N` are isomorphisms (as for closed immersions), that `c` and `c'` are
isomorphisms with `A C₀ ≅ C₀'`, and that the projection morphisms `H (P' N) ⊗ C₀ ⟶ H (P' N ⊗ A C₀)`
and `H' (Q' N) ⊗ D₀ ⟶ H' (Q' N ⊗ A' D₀)` are isomorphisms (projection formula). Then the Künneth
map of `F ⊣ G` at `M` is an isomorphism if the Künneth map of `F' ⊣ G'` at `N` is.

Neither the isomorphisms `P M ≅ H (P' N)`, `Q M ≅ H' (Q' N)` and `A C₀ ≅ C₀'` nor `e` and `e'`
need to be compatible: the Künneth map at `M` is identified with `H` of a Künneth map at `N`
(`homEquiv_δ_tensorHom_comp_map_projectionMorphism`) with modified, but still invertible,
components. -/
lemma isIso_kunnethNatTrans_app_of_pushforward
    (hθ : ∀ X Y : D, θ.hom.app (X ⊗ Y) ≫ F'.map (δ A X Y) ≫ δ F' (A.obj X) (A.obj Y) =
      A'.map (δ F X Y) ≫ δ A' (F.obj X) (F.obj Y) ≫ (θ.hom.app X ⊗ₘ θ.hom.app Y))
    {𝒳 : Type u₅} [Category.{v₅} 𝒳] {P : 𝒳 ⥤ D} {Q : 𝒳 ⥤ C} (e : P ⋙ F ≅ Q)
    {𝒵 : Type u₆} [Category.{v₆} 𝒵] {P' : 𝒵 ⥤ D'} {Q' : 𝒵 ⥤ C'} (e' : P' ⋙ F' ≅ Q')
    {C₀ : D} {D₀ : C} (c : F.obj C₀ ⟶ D₀) [IsIso c] {C₀' : D'} {D₀' : C'}
    (c' : F'.obj C₀' ⟶ D₀') [IsIso c'] {M : 𝒳} {N : 𝒵} (β : P.obj M ≅ H.obj (P'.obj N))
    (β' : Q.obj M ≅ H'.obj (Q'.obj N)) (φ : A.obj C₀ ≅ C₀')
    [IsIso (adjA.counit.app (P'.obj N))] [IsIso (adjA'.counit.app (Q'.obj N))]
    [IsIso (adjA.projectionMorphism (P'.obj N) C₀)]
    [IsIso (adjA'.projectionMorphism (Q'.obj N) D₀)]
    (h : IsIso ((adjF'.kunnethNatTrans e' c').app N)) :
    IsIso ((adjF.kunnethNatTrans e c).app M) := by
  rw [kunnethNatTrans_app] at h ⊢
  let ε : F.obj (H.obj (P'.obj N)) ⟶ H'.obj (Q'.obj N) := F.map β.inv ≫ e.hom.app M ≫ β'.hom
  let ε' : F'.obj (P'.obj N) ⟶ Q'.obj N := inv (F'.map (adjA.counit.app (P'.obj N))) ≫
    θ.inv.app _ ≫ A'.map ε ≫ adjA'.counit.app (Q'.obj N)
  let ψ : D₀' ⟶ A'.obj D₀ := inv c' ≫ F'.map φ.inv ≫ θ.inv.app C₀ ≫ A'.map c
  have hK : adjF.homEquiv _ _ (δ F (P.obj M) C₀ ≫ (e.hom.app M ⊗ₘ c)) =
      β.hom ▷ C₀ ≫ adjF.homEquiv _ _ (δ F _ C₀ ≫ (ε ⊗ₘ c)) ≫ G.map (β'.inv ▷ D₀) := by
    rw [← homEquiv_δ_tensorHom_comp_right, ← homEquiv_δ_tensorHom_map_comp]
    simp [ε]
  have hK' : adjF'.homEquiv _ _ (δ F' (P'.obj N) C₀' ≫ (ε' ⊗ₘ c')) =
      adjF'.homEquiv _ _ (δ F' (P'.obj N) C₀' ≫ (e'.hom.app N ⊗ₘ c')) ≫
        G'.map ((inv (e'.hom.app N) ≫ ε') ▷ D₀') := by
    rw [← homEquiv_δ_tensorHom_comp_right, IsIso.hom_inv_id_assoc]
  have key := homEquiv_δ_tensorHom_comp_map_projectionMorphism adjF adjF' adjA adjA' θ hθ ε c ε'
    c' φ.hom ψ (by simp [ε']) (by simp [ψ])
  rw [hK, isIso_comp_left_iff, isIso_comp_right_iff,
    ← isIso_comp_right_iff _ (G.map (adjA'.projectionMorphism _ D₀)), key, hK']
  infer_instance

end Pushforward

end CategoryTheory.Adjunction
