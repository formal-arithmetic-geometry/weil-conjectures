/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.PoincareDuality.Abstract

/-!

# Composition and transport of projection morphisms

For adjunctions `F ⊣ G` with `F` oplax monoidal (the pullback–pushforward adjunctions of proper
morphisms) and `P ⊣ S` with `S` lax monoidal (the extension by zero along open immersions), the
projection morphism and the projection comparison of a composite adjunction are the composites of
those of the factors (`CategoryTheory.Adjunction.projectionMorphism_comp`,
`CategoryTheory.Adjunction.projectionComparison_comp`), and the projection morphism is transported
along an isomorphism of left adjoints compatible with the comultiplications
(`CategoryTheory.Adjunction.projectionMorphism_eq_of_iso`). These are the formal parts of the
composition clause of the coherence of the projection formula (blueprint `prop-sf-pf-coherence`).

-/

@[expose] public section
open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃]
  {F₁ : C₂ ⥤ C₁} {G₁ : C₁ ⥤ C₂} {F₂ : C₃ ⥤ C₂} {G₂ : C₂ ⥤ C₃}
  [F₁.OplaxMonoidal] [F₂.OplaxMonoidal] (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂)

/-- The projection morphism of a composite adjunction is the composite of the projection
morphisms. -/
lemma projectionMorphism_comp (A : C₁) (B : C₃) :
    (a₂.comp a₁).projectionMorphism A B =
      a₂.projectionMorphism (G₁.obj A) B ≫ G₂.map (a₁.projectionMorphism A (F₂.obj B)) := by
  rw [projectionMorphism, projectionMorphism, projectionMorphism, comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [← homEquiv_naturality_right, ← homEquiv_naturality_left]
  simp [Functor.OplaxMonoidal.comp_δ, comp_counit_app, δ_natural_left_assoc]

section Comparison

variable {P₁ : C₁ ⥤ C₂} {S₁ : C₂ ⥤ C₁} {P₂ : C₂ ⥤ C₃} {S₂ : C₃ ⥤ C₂}
  [S₁.LaxMonoidal] [S₂.LaxMonoidal] (b₁ : P₁ ⊣ S₁) (b₂ : P₂ ⊣ S₂)

open Functor.LaxMonoidal in
/-- The projection comparison of a composite adjunction is the composite of the projection
comparisons. -/
lemma projectionComparison_comp (M : C₁) (N : C₃) :
    (b₁.comp b₂).projectionComparison M N =
      P₂.map (b₁.projectionComparison M (S₂.obj N)) ≫ b₂.projectionComparison (P₁.obj M) N := by
  rw [projectionComparison, projectionComparison, projectionComparison, comp_homEquiv]
  dsimp only [Equiv.symm_trans_apply]
  rw [← homEquiv_naturality_left_symm, ← homEquiv_naturality_right_symm]
  congr 1
  simp [Functor.LaxMonoidal.comp_μ, comp_unit_app]

end Comparison

section Transport

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] [MonoidalCategory D₁] [MonoidalCategory D₂]
  {F F' : D₂ ⥤ D₁} {G G' : D₁ ⥤ D₂} [F.OplaxMonoidal] [F'.OplaxMonoidal]
  (a : F ⊣ G) (a' : F' ⊣ G') (e : F ≅ F')

/-- The projection morphism is transported along an isomorphism `e : F ≅ F'` of oplax monoidal
left adjoints compatible with the comultiplications, through the conjugate `G' ≅ G`. -/
lemma projectionMorphism_eq_of_iso
    (he : ∀ X Y, δ F X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) = e.hom.app (X ⊗ Y) ≫ δ F' X Y)
    (A : D₁) (B : D₂) :
    a.projectionMorphism A B =
      (conjugateIsoEquiv a' a e).inv.app A ▷ B ≫ a'.projectionMorphism A B ≫
        (conjugateIsoEquiv a' a e).hom.app _ ≫ G.map (A ◁ e.inv.app B) := by
  have h1 : ∀ Z, F.map ((conjugateIsoEquiv a' a e).hom.app Z) ≫ a.counit.app Z =
      e.hom.app (G'.obj Z) ≫ a'.counit.app Z := fun Z ↦ conjugateEquiv_counit a' a e.hom Z
  have h2 : e.hom.app (G.obj A) ≫ F'.map ((conjugateIsoEquiv a' a e).inv.app A) ≫
      a'.counit.app A = a.counit.app A := by
    rw [show (conjugateIsoEquiv a' a e).inv = conjugateEquiv a a' e.inv from rfl,
      conjugateEquiv_counit, Iso.hom_inv_id_app_assoc]
  have h3 : F'.map (a'.projectionMorphism A B) ≫ a'.counit.app _ =
      δ F' (G'.obj A) B ≫ a'.counit.app A ▷ F'.obj B := by
    refine (a'.homEquiv_counit (g := a'.projectionMorphism A B)).symm.trans ?_
    rw [projectionMorphism, Equiv.symm_apply_apply]
  apply (a.homEquiv _ _).symm.injective
  rw [projectionMorphism, Equiv.symm_apply_apply, homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality]
  rw [reassoc_of% (h1 (A ⊗ F'.obj B))]
  rw [e.hom.naturality_assoc, e.hom.naturality_assoc, reassoc_of% h3,
    ← δ_natural_left_assoc, ← reassoc_of% (he (G.obj A) B)]
  rw [← h2]
  simp only [tensorHom_def, Category.assoc, comp_whiskerRight, whisker_exchange_assoc,
    ← whiskerLeft_comp, Iso.hom_inv_id_app, whiskerLeft_id, Category.comp_id]

end Transport

section TransportComparison

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] [MonoidalCategory D₁] [MonoidalCategory D₂]
  {P P' : D₁ ⥤ D₂} {S S' : D₂ ⥤ D₁} [S.LaxMonoidal] [S'.LaxMonoidal]
  (b : P ⊣ S) (b' : P' ⊣ S') (e : S ≅ S')

open Functor.LaxMonoidal in
/-- The projection comparison is transported along an isomorphism `e : S ≅ S'` of lax monoidal
right adjoints compatible with the multiplications, through the conjugate `P' ≅ P`. -/
lemma projectionComparison_eq_of_iso
    (he : ∀ X Y, μ S X Y ≫ e.hom.app (X ⊗ Y) = (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ S' X Y)
    (M : D₁) (N : D₂) :
    b.projectionComparison M N =
      ((conjugateIsoEquiv b b').symm e).inv.app (M ⊗ S.obj N) ≫ P'.map (M ◁ e.hom.app N) ≫
        b'.projectionComparison M N ≫ ((conjugateIsoEquiv b b').symm e).hom.app M ▷ N := by
  set γ := (conjugateIsoEquiv b b').symm e with hγ
  have hu : ∀ X, b'.unit.app X ≫ S'.map (γ.hom.app X) = b.unit.app X ≫ e.hom.app (P.obj X) := by
    intro X
    have h := unit_conjugateEquiv b b' γ.hom X
    rw [show conjugateEquiv b b' γ.hom = e.hom by
      rw [hγ, ← conjugateIsoEquiv_apply_hom, Equiv.apply_symm_apply]] at h
    exact h.symm
  have hpc : b.homEquiv _ _ (b.projectionComparison M N) =
      b.unit.app M ▷ S.obj N ≫ μ S (P.obj M) N := by
    rw [projectionComparison, Equiv.apply_symm_apply]
  have hpc' : b'.homEquiv _ _ (b'.projectionComparison M N) =
      b'.unit.app M ▷ S'.obj N ≫ μ S' (P'.obj M) N := by
    rw [projectionComparison, Equiv.apply_symm_apply]
  rw [← cancel_epi (γ.hom.app (M ⊗ S.obj N)), Iso.hom_inv_id_app_assoc]
  apply (b'.homEquiv _ _).injective
  conv_lhs => rw [homEquiv_unit, S'.map_comp, ← Category.assoc, hu, Category.assoc,
    ← e.hom.naturality,
    ← Category.assoc, ← homEquiv_unit, hpc]
  conv_rhs => rw [homEquiv_naturality_left, homEquiv_naturality_right, hpc']
  rw [Category.assoc, Category.assoc, ← μ_natural_left, ← comp_whiskerRight_assoc, hu,
    comp_whiskerRight_assoc, whisker_exchange_assoc, ← tensorHom_def'_assoc, ← he]

end TransportComparison

section Combined

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃]

/-- An isomorphism of monoidal functors compatible with the comultiplications is compatible with
the multiplications. -/
lemma μ_comp_hom_app_eq_of_δ {F F' : C₁ ⥤ C₂} [F.Monoidal] [F'.Monoidal] (e : F ≅ F')
    (he : ∀ X Y, δ F X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) = e.hom.app (X ⊗ Y) ≫ δ F' X Y)
    (X Y : C₁) :
    Functor.LaxMonoidal.μ F X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ Functor.LaxMonoidal.μ F' X Y := by
  rw [← cancel_mono (δ F' X Y), Category.assoc, Category.assoc, Functor.Monoidal.μ_δ,
    Category.comp_id, ← he, Functor.Monoidal.μ_δ_assoc]

/-- `μ_comp_hom_app_eq_of_δ` for an isomorphism with a composite, with the comultiplication and
multiplication of the composite written out. -/
lemma μ_comp_hom_app_eq_of_δ_comp {F : C₁ ⥤ C₃} {F₁ : C₁ ⥤ C₂} {F₂ : C₂ ⥤ C₃} [F.Monoidal]
    [F₁.Monoidal] [F₂.Monoidal] (e : F ≅ F₁ ⋙ F₂)
    (he : ∀ X Y, δ F X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) =
      e.hom.app (X ⊗ Y) ≫ F₂.map (δ F₁ X Y) ≫ δ F₂ (F₁.obj X) (F₁.obj Y)) (X Y : C₁) :
    Functor.LaxMonoidal.μ F X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ Functor.LaxMonoidal.μ F₂ (F₁.obj X) (F₁.obj Y) ≫
        F₂.map (Functor.LaxMonoidal.μ F₁ X Y) := by
  have := μ_comp_hom_app_eq_of_δ e (fun X Y ↦ by rw [Functor.OplaxMonoidal.comp_δ]; exact he X Y)
    X Y
  rwa [Functor.LaxMonoidal.comp_μ] at this

/-- The projection comparison of `P ⊣ S` with `S ≅ S₂ ⋙ S₁` a monoidal isomorphism is the
composite of the projection comparisons of `P₁ ⊣ S₁` and `P₂ ⊣ S₂`, read through `S ≅ S₂ ⋙ S₁`
and its conjugate. -/
lemma projectionComparison_eq_of_iso_comp {P : C₁ ⥤ C₃} {S : C₃ ⥤ C₁} {P₁ : C₁ ⥤ C₂}
    {S₁ : C₂ ⥤ C₁} {P₂ : C₂ ⥤ C₃} {S₂ : C₃ ⥤ C₂} [S.Monoidal] [S₁.Monoidal] [S₂.Monoidal]
    (b : P ⊣ S) (b₁ : P₁ ⊣ S₁) (b₂ : P₂ ⊣ S₂) (e : S ≅ S₂ ⋙ S₁)
    (he : ∀ X Y, δ S X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) = e.hom.app (X ⊗ Y) ≫ δ (S₂ ⋙ S₁) X Y)
    (M : C₁) (N : C₃) :
    b.projectionComparison M N =
      ((conjugateIsoEquiv b (b₁.comp b₂)).symm e).inv.app (M ⊗ S.obj N) ≫
        P₂.map (P₁.map (M ◁ e.hom.app N)) ≫ P₂.map (b₁.projectionComparison M (S₂.obj N)) ≫
        b₂.projectionComparison (P₁.obj M) N ≫
        ((conjugateIsoEquiv b (b₁.comp b₂)).symm e).hom.app M ▷ N := by
  rw [projectionComparison_eq_of_iso b (b₁.comp b₂) e (μ_comp_hom_app_eq_of_δ e he),
    projectionComparison_comp]
  simp only [Functor.comp_map, Category.assoc]

end Combined

section Restriction

variable {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂]
  {Pi : C₀ ⥤ C₁} {Si : C₁ ⥤ C₀} {Pi₁ : C₀ ⥤ C₂} {Si₁ : C₂ ⥤ C₀} {Fh : C₂ ⥤ C₁}
  [Si.LaxMonoidal] [Si₁.LaxMonoidal] [Fh.LaxMonoidal]
  (bi : Pi ⊣ Si) (bi₁ : Pi₁ ⊣ Si₁) (e : Si₁ ≅ Fh ⋙ Si)

/-- The *restriction comparison* `i_! ⟶ h^* i₁_!` for open immersions `i : X ⟶ Z`,
`i₁ : X ⟶ Z₁` and `h : Z ⟶ Z₁` with `i ≫ h = i₁`, through `e : i₁^* ≅ h^* ⋙ i^*`: the unit of
`i₁_! ⊣ i₁^*`, `e`, and the counit of `i_! ⊣ i^*`. -/
def restrictionComparison (M : C₀) : Pi.obj M ⟶ Fh.obj (Pi₁.obj M) :=
  Pi.map (bi₁.unit.app M ≫ e.hom.app (Pi₁.obj M)) ≫ bi.counit.app _

open Functor.LaxMonoidal in
/-- **The restriction comparison intertwines the projection comparisons**: for `e` compatible with
the multiplications, `q_i` followed by `ρ ⊗ 𝟙` and the multiplication of `h^*` is `ρ` followed
by `h^* q_{i₁}`, through `e`. -/
lemma projectionComparison_comp_restrictionComparison
    (he : ∀ X Y, μ Si₁ X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ Si (Fh.obj X) (Fh.obj Y) ≫ Si.map (μ Fh X Y))
    (K : C₀) (B : C₂) :
    bi.projectionComparison K (Fh.obj B) ≫ restrictionComparison bi bi₁ e K ▷ Fh.obj B ≫
        μ Fh (Pi₁.obj K) B =
      Pi.map (K ◁ e.inv.app B) ≫ restrictionComparison bi bi₁ e (K ⊗ Si₁.obj B) ≫
        Fh.map (bi₁.projectionComparison K B) := by
  have hρ : ∀ M, bi.homEquiv _ _ (restrictionComparison bi bi₁ e M) =
      bi₁.unit.app M ≫ e.hom.app (Pi₁.obj M) := fun M ↦ by
    rw [restrictionComparison, ← homEquiv_counit, Equiv.apply_symm_apply]
  have hq : bi.homEquiv _ _ (bi.projectionComparison K (Fh.obj B)) =
      bi.unit.app K ▷ Si.obj (Fh.obj B) ≫ μ Si (Pi.obj K) (Fh.obj B) := by
    rw [projectionComparison, Equiv.apply_symm_apply]
  have hq₁ : bi₁.homEquiv _ _ (bi₁.projectionComparison K B) =
      bi₁.unit.app K ▷ Si₁.obj B ≫ μ Si₁ (Pi₁.obj K) B := by
    rw [projectionComparison, Equiv.apply_symm_apply]
  have hn := e.hom.naturality (bi₁.projectionComparison K B)
  simp only [Functor.comp_map] at hn
  apply (bi.homEquiv _ _).injective
  rw [homEquiv_naturality_right, hq, homEquiv_naturality_left, homEquiv_naturality_right, hρ]
  conv_rhs => rw [Category.assoc, ← hn, ← Category.assoc (bi₁.unit.app _)]
  erw [← bi₁.homEquiv_unit]
  erw [hq₁]
  simp only [Category.assoc]
  rw [he]
  rw [Si.map_comp, ← μ_natural_left_assoc, ← comp_whiskerRight_assoc]
  erw [← bi.homEquiv_unit, hρ]
  rw [tensorHom_def]
  simp only [comp_whiskerRight, Category.assoc, whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    Iso.inv_hom_id_app, whiskerLeft_id, Category.id_comp]
  rfl

end Restriction

section Refinement

variable {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂]
  {Pi : C₀ ⥤ C₁} {Si : C₁ ⥤ C₀} {Pi₁ : C₀ ⥤ C₂} {Si₁ : C₂ ⥤ C₀} {Fh : C₂ ⥤ C₁}
  [Si.LaxMonoidal] [Si₁.LaxMonoidal] [Fh.Monoidal]
  (bi : Pi ⊣ Si) (bi₁ : Pi₁ ⊣ Si₁) (e : Si₁ ≅ Fh ⋙ Si)

open Functor.LaxMonoidal in
/-- **The refinement comparison intertwines the projection formulas**: for `Fh ⊣ Gh` (the
proper `h`) with `Fh` monoidal and the restriction comparison `ρ'` invertible, the comparison
`ρ = η_h ≫ Gh ρ'⁻¹ : i₁_! ⟶ h_* i_!` carries `q_{i₁}` followed by the projection morphism of `h`
to `h_*` of `q_i`. -/
lemma projectionComparison_comp_refinement {Gh : C₁ ⥤ C₂} (ah : Fh ⊣ Gh)
    [∀ M, IsIso (restrictionComparison bi bi₁ e M)]
    (he : ∀ X Y, μ Si₁ X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ Si (Fh.obj X) (Fh.obj Y) ≫ Si.map (μ Fh X Y))
    (K : C₀) (B : C₂) :
    bi₁.projectionComparison K B ≫
        (ah.unit.app (Pi₁.obj K) ≫ Gh.map (inv (restrictionComparison bi bi₁ e K))) ▷ B ≫
        ah.projectionMorphism (Pi.obj K) B =
      (ah.unit.app (Pi₁.obj (K ⊗ Si₁.obj B)) ≫
        Gh.map (inv (restrictionComparison bi bi₁ e (K ⊗ Si₁.obj B)))) ≫
        Gh.map (Pi.map (K ◁ e.hom.app B) ≫ bi.projectionComparison K (Fh.obj B)) := by
  have h6 := projectionComparison_comp_restrictionComparison bi bi₁ e he K B
  have h6' : inv (restrictionComparison bi bi₁ e (K ⊗ Si₁.obj B)) ≫ Pi.map (K ◁ e.hom.app B) ≫
      bi.projectionComparison K (Fh.obj B) =
      Fh.map (bi₁.projectionComparison K B) ≫ δ Fh (Pi₁.obj K) B ≫
        inv (restrictionComparison bi bi₁ e K) ▷ Fh.obj B := by
    rw [IsIso.inv_comp_eq, ← cancel_mono (restrictionComparison bi bi₁ e K ▷ Fh.obj B)]
    simp only [Category.assoc, ← comp_whiskerRight, IsIso.inv_hom_id, id_whiskerRight,
      Category.comp_id]
    rw [← cancel_mono (μ Fh (Pi₁.obj K) B)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
    rw [h6]
    simp only [← Pi.map_comp_assoc, ← whiskerLeft_comp, Iso.hom_inv_id_app, whiskerLeft_id,
      Pi.map_id, Category.id_comp]
  apply (ah.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, projectionMorphism, homEquiv_unit, Functor.map_comp,
    Category.assoc, Adjunction.counit_naturality, Adjunction.counit_naturality_assoc,
    Adjunction.left_triangle_components_assoc]
  rw [h6', ← δ_natural_left_assoc, ← comp_whiskerRight, Functor.map_comp, Category.assoc]
  erw [ah.counit_naturality, ah.left_triangle_components_assoc]
  rfl

end Refinement

section NaturalLeft

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] [MonoidalCategory D₁] [MonoidalCategory D₂]
  {F : D₂ ⥤ D₁} {G : D₁ ⥤ D₂} [F.OplaxMonoidal] (adj : F ⊣ G)

/-- The projection morphism is natural in its first variable. -/
@[reassoc]
lemma projectionMorphism_natural_left {A A' : D₁} (a : A ⟶ A') (B : D₂) :
    G.map a ▷ B ≫ adj.projectionMorphism A' B =
      adj.projectionMorphism A B ≫ G.map (a ▷ F.obj B) := by
  rw [projectionMorphism, projectionMorphism, ← homEquiv_naturality_left,
    ← homEquiv_naturality_right]
  congr 1
  rw [← δ_natural_left_assoc, Category.assoc, ← comp_whiskerRight]
  erw [adj.counit_naturality]
  rw [comp_whiskerRight]

end NaturalLeft

section Independence

variable {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃]
  {Pi : C₀ ⥤ C₁} {Si : C₁ ⥤ C₀} {Pi₁ : C₀ ⥤ C₂} {Si₁ : C₂ ⥤ C₀} {Fh : C₂ ⥤ C₁}
  {Gh : C₁ ⥤ C₂} {Fp : C₃ ⥤ C₁} {Gp : C₁ ⥤ C₃} {Fp₁ : C₃ ⥤ C₂} {Gp₁ : C₂ ⥤ C₃} {Ff : C₃ ⥤ C₀}
  [Si.LaxMonoidal] [Si₁.LaxMonoidal] [Fh.Monoidal] [Fp.Monoidal] [Fp₁.Monoidal]
  (bi : Pi ⊣ Si) (bi₁ : Pi₁ ⊣ Si₁) (ah : Fh ⊣ Gh) (ap : Fp ⊣ Gp) (ap₁ : Fp₁ ⊣ Gp₁)

/-- The *exceptional projection morphism* `PF_{f, (i, p)} : p_* i_! K ⊗ B ⟶ p_* i_! (K ⊗ f^* B)`
of a compactification `f = i ≫ p` (`i_! ⊣ i^*` open, `p^* ⊣ p_*` proper, `cf : f^* ≅ p^* ⋙ i^*`):
the projection morphism of `p` at `i_! K` followed by `p_*` of the inverse of the projection
comparison of `i`. -/
noncomputable def exceptionalProjection (cf : Ff ≅ Fp ⋙ Si)
    [∀ K N, IsIso (bi.projectionComparison K N)] (K : C₀) (B : C₃) :
    Gp.obj (Pi.obj K) ⊗ B ⟶ Gp.obj (Pi.obj (K ⊗ Ff.obj B)) :=
  ap.projectionMorphism (Pi.obj K) B ≫
    Gp.map (inv (bi.projectionComparison K (Fp.obj B)) ≫ Pi.map (K ◁ cf.inv.app B))

variable {bi bi₁} in
omit [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂] [Si.LaxMonoidal]
  [Si₁.LaxMonoidal] [Fh.Monoidal] in
lemma restrictionComparison_naturality (e : Si₁ ≅ Fh ⋙ Si) {M M' : C₀} (x : M ⟶ M') :
    Pi.map x ≫ restrictionComparison bi bi₁ e M' =
      restrictionComparison bi bi₁ e M ≫ Fh.map (Pi₁.map x) := by
  simp only [restrictionComparison, ← Pi.map_comp_assoc, Category.assoc]
  rw [← bi₁.unit_naturality_assoc, e.hom.naturality]
  simp

open Functor.LaxMonoidal in
/-- **Independence of the compactification** (blueprint `prop-sf-pf-coherence`, independence
clause): for a refinement `h : Z ⟶ Z₁` of compactifications `f = i₁ ≫ p₁ = i ≫ p` with
`i ≫ h = i₁` and `h ≫ p₁ = p`, the refinement isomorphism
`p₁_* i₁_! ⟶ p₁_* h_* i_! ≅ p_* i_!` carries the exceptional projection morphism of `(i₁, p₁)` to
that of `(i, p)`, provided the composition isomorphisms are coherent (`hcoh`). -/
theorem exceptionalProjection_comp_refinement (e : Si₁ ≅ Fh ⋙ Si) (c : Fp ≅ Fp₁ ⋙ Fh)
    (cf : Ff ≅ Fp ⋙ Si) (cf₁ : Ff ≅ Fp₁ ⋙ Si₁)
    [∀ M, IsIso (restrictionComparison bi bi₁ e M)]
    [∀ K N, IsIso (bi.projectionComparison K N)] [∀ K N, IsIso (bi₁.projectionComparison K N)]
    (he : ∀ X Y, μ Si₁ X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ Si (Fh.obj X) (Fh.obj Y) ≫ Si.map (μ Fh X Y))
    (hc : ∀ X Y, δ Fp X Y ≫ (c.hom.app X ⊗ₘ c.hom.app Y) =
      c.hom.app (X ⊗ Y) ≫ Fh.map (δ Fp₁ X Y) ≫ δ Fh (Fp₁.obj X) (Fp₁.obj Y))
    (hcoh : ∀ B, cf.hom.app B ≫ Si.map (c.hom.app B) = cf₁.hom.app B ≫ e.hom.app (Fp₁.obj B))
    (K : C₀) (B : C₃) :
    exceptionalProjection bi₁ ap₁ cf₁ K B ≫
        (Gp₁.map (ah.unit.app (Pi₁.obj (K ⊗ Ff.obj B)) ≫
          Gh.map (inv (restrictionComparison bi bi₁ e (K ⊗ Ff.obj B)))) ≫
          (conjugateIsoEquiv (ap₁.comp ah) ap c).hom.app _) =
      (Gp₁.map (ah.unit.app (Pi₁.obj K) ≫ Gh.map (inv (restrictionComparison bi bi₁ e K))) ≫
          (conjugateIsoEquiv (ap₁.comp ah) ap c).hom.app _) ▷ B ≫
        exceptionalProjection bi ap cf K B := by
  have hcf : cf₁.inv.app B = e.hom.app (Fp₁.obj B) ≫ Si.map (c.inv.app B) ≫ cf.inv.app B := by
    rw [← cancel_epi (cf₁.hom.app B), Iso.hom_inv_id_app, ← reassoc_of% (hcoh B),
      ← Si.map_comp_assoc, Iso.hom_inv_id_app, Si.map_id, Category.id_comp, Iso.hom_inv_id_app]
  have hPi : Pi.map (K ◁ cf₁.inv.app B) = Pi.map (K ◁ e.hom.app (Fp₁.obj B)) ≫
      bi.projectionComparison K (Fh.obj (Fp₁.obj B)) ≫ Pi.obj K ◁ c.inv.app B ≫
      inv (bi.projectionComparison K (Fp.obj B)) ≫ Pi.map (K ◁ cf.inv.app B) := by
    rw [← bi.projectionComparison_natural_right_assoc, IsIso.hom_inv_id_assoc, ← Pi.map_comp,
      ← Pi.map_comp, ← whiskerLeft_comp, ← whiskerLeft_comp, hcf]
  have hρn : ∀ {M M' : C₀} (x : M ⟶ M'),
      Pi₁.map x ≫ ah.unit.app (Pi₁.obj M') ≫ Gh.map (inv (restrictionComparison bi bi₁ e M')) =
        (ah.unit.app (Pi₁.obj M) ≫ Gh.map (inv (restrictionComparison bi bi₁ e M))) ≫
          Gh.map (Pi.map x) := by
    intro M M' x
    have hn := restrictionComparison_naturality (bi := bi) (bi₁ := bi₁) e x
    have hn' : inv (restrictionComparison bi bi₁ e M) ≫ Pi.map x =
        Fh.map (Pi₁.map x) ≫ inv (restrictionComparison bi bi₁ e M') := by
      rw [IsIso.inv_comp_eq, ← reassoc_of% hn, IsIso.hom_inv_id, Category.comp_id]
    rw [← ah.unit_naturality_assoc, Category.assoc, ← Gh.map_comp, ← Gh.map_comp, hn']
  have h8 := projectionComparison_comp_refinement bi bi₁ e ah he K (Fp₁.obj B)
  have h8' : (ah.unit.app (Pi₁.obj K) ≫ Gh.map (inv (restrictionComparison bi bi₁ e K))) ▷
        Fp₁.obj B ≫ ah.projectionMorphism (Pi.obj K) (Fp₁.obj B) =
      inv (bi₁.projectionComparison K (Fp₁.obj B)) ≫
        (ah.unit.app (Pi₁.obj (K ⊗ Si₁.obj (Fp₁.obj B))) ≫
          Gh.map (inv (restrictionComparison bi bi₁ e (K ⊗ Si₁.obj (Fp₁.obj B))))) ≫
        Gh.map (Pi.map (K ◁ e.hom.app (Fp₁.obj B)) ≫
          bi.projectionComparison K (Fh.obj (Fp₁.obj B))) := by
    rw [IsIso.eq_inv_comp, ← h8]
  have hPM := projectionMorphism_eq_of_iso ap (ap₁.comp ah) c
    (fun X Y ↦ by rw [Functor.OplaxMonoidal.comp_δ]; exact hc X Y) (Pi.obj K) B
  rw [projectionMorphism_comp] at hPM
  rw [exceptionalProjection, exceptionalProjection, hPM]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc ((conjugateIsoEquiv (ap₁.comp ah) ap c).hom.app _),
    Iso.hom_inv_id_app, id_whiskerRight, Category.id_comp, projectionMorphism_natural_left_assoc]
  congr 1
  have hγn : ∀ {S T : C₁} (s : S ⟶ T), Gp₁.map (Gh.map s) ≫
      (conjugateIsoEquiv (ap₁.comp ah) ap c).hom.app T =
        (conjugateIsoEquiv (ap₁.comp ah) ap c).hom.app S ≫ Gp.map s :=
    fun s ↦ (conjugateIsoEquiv (ap₁.comp ah) ap c).hom.naturality s
  rw [← Gp₁.map_comp_assoc ((_ ≫ _) ▷ _), h8', ← Gp₁.map_comp_assoc (inv _ ≫ _), Category.assoc,
    hρn]
  simp only [Functor.map_comp, Category.assoc, hγn]
  rw [hPi]
  simp only [Functor.map_comp]
  erw [reassoc_of% (hγn (bi.projectionComparison K (Fh.obj (Fp₁.obj B)))),
    reassoc_of% (hγn (Pi.map (K ◁ e.hom.app (Fp₁.obj B))))]

end Independence

end CategoryTheory.Adjunction

namespace CategoryTheory.ObjectProperty

open MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C] {D : Type*} [Category D]
  [MonoidalCategory D] {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D}
  [Q.IsMonoidal] (F : C ⥤ D) [F.Monoidal] (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
variable {G : D ⥤ C} (adj : F ⊣ G) (hG : ∀ Y : Q.FullSubcategory, P (G.obj Y.obj))

/-- The projection morphism of the restriction of an adjunction `F ⊣ G` with `F` strong monoidal
to full monoidal subcategories is the projection morphism of `F ⊣ G`. -/
lemma projectionMorphism_restrictFullyFaithful_hom (A : Q.FullSubcategory)
    (B : P.FullSubcategory) :
    ((adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
        (Q.liftCompιIso (P.ι ⋙ F) hF).symm (P.liftCompιIso (Q.ι ⋙ G) hG).symm).projectionMorphism
          A B).hom =
      adj.projectionMorphism A.obj B.obj := by
  have hε := Adjunction.map_restrictFullyFaithful_counit_app adj P.fullyFaithfulι
    Q.fullyFaithfulι (Q.liftCompιIso (P.ι ⋙ F) hF).symm (P.liftCompιIso (Q.ι ⋙ G) hG).symm A
  simp only [liftCompιIso, Iso.refl_symm, Iso.refl_inv, NatTrans.id_app, Category.id_comp, ι_map]
    at hε
  rw [Adjunction.projectionMorphism, Adjunction.restrictFullyFaithful_homEquiv_apply,
    Adjunction.projectionMorphism, Adjunction.homEquiv_unit]
  simp [liftCompιIso, δ_monoidalLift_hom, hε]

section Comparison

variable {G : D ⥤ C} (b : G ⊣ F) (hG : ∀ Y : Q.FullSubcategory, P (G.obj Y.obj))

/-- The projection comparison of the restriction of an adjunction `G ⊣ F` with `F` strong monoidal
to full monoidal subcategories is the projection comparison of `G ⊣ F`. -/
lemma projectionComparison_restrictFullyFaithful_hom (M : Q.FullSubcategory)
    (N : P.FullSubcategory) :
    ((b.restrictFullyFaithful Q.fullyFaithfulι P.fullyFaithfulι
        (P.liftCompιIso (Q.ι ⋙ G) hG).symm (Q.liftCompιIso (P.ι ⋙ F) hF).symm).projectionComparison
          M N).hom =
      b.projectionComparison M.obj N.obj := by
  have hη := Adjunction.map_restrictFullyFaithful_unit_app b Q.fullyFaithfulι
    P.fullyFaithfulι (P.liftCompιIso (Q.ι ⋙ G) hG).symm (Q.liftCompιIso (P.ι ⋙ F) hF).symm M
  simp only [liftCompιIso, Iso.refl_symm, Iso.refl_hom, NatTrans.id_app, ι_map] at hη
  have hε := Adjunction.map_restrictFullyFaithful_counit_app b Q.fullyFaithfulι
    P.fullyFaithfulι (P.liftCompιIso (Q.ι ⋙ G) hG).symm (Q.liftCompιIso (P.ι ⋙ F) hF).symm
    ((P.lift (Q.ι ⋙ G) hG).obj M ⊗ N)
  simp only [liftCompιIso, Iso.refl_symm, Iso.refl_inv, NatTrans.id_app, Category.id_comp, ι_map]
    at hε
  rw [Adjunction.projectionComparison, Adjunction.projectionComparison, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_counit]
  simp only [liftCompιIso, Iso.refl_symm] at hη hε ⊢
  simp [hη, hε, μ_monoidalLift_hom]

end Comparison

end CategoryTheory.ObjectProperty
