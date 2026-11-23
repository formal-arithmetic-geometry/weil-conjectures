/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Transitivity of squares of left derived functors

Consider three rows `C₁ ⥤ C₂ ⥤ C₃` (functors `E₁₂`, `E₂₃`, `E₁₃`) and `C'₁ ⥤ C'₂ ⥤ C'₃`
(functors `F₁₂`, `F₂₃`, `F₁₃`), linked by vertical functors `pᵢ : Cᵢ ⥤ C'ᵢ`, with squares
`eᵢⱼ : Eᵢⱼ ⋙ pⱼ ⟶ pᵢ ⋙ Fᵢⱼ` and comparisons `c : E₁₂ ⋙ E₂₃ ⟶ E₁₃`, `c' : F₁₂ ⋙ F₂₃ ⟶ F₁₃`
compatible with the squares. Suppose that all these functors have left derived functors, and that
the squares `Φᵢⱼ` and comparisons `τ`, `τ'` between the left derived functors are induced by the
underived ones through the counits. Then the left derived squares are compatible with `τ`, `τ'`
(`CategoryTheory.Functor.leftDerived_square_trans`), as soon as
`Lp₁ ⋙ LF₁₃` is a left derived functor of `p₁ ⋙ F₁₃`.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C₁ C₂ C₃ C'₁ C'₂ C'₃ D₁ D₂ D₃ D'₁ D'₂ D'₃ : Type*} [Category* C₁] [Category* C₂]
  [Category* C₃] [Category* C'₁] [Category* C'₂] [Category* C'₃] [Category* D₁] [Category* D₂]
  [Category* D₃] [Category* D'₁] [Category* D'₂] [Category* D'₃]
  {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂} {Q₃ : C₃ ⥤ D₃} {Q'₁ : C'₁ ⥤ D'₁} {Q'₂ : C'₂ ⥤ D'₂}
  {Q'₃ : C'₃ ⥤ D'₃}
  {E₁₂ : C₁ ⥤ C₂} {E₂₃ : C₂ ⥤ C₃} {E₁₃ : C₁ ⥤ C₃} {F₁₂ : C'₁ ⥤ C'₂} {F₂₃ : C'₂ ⥤ C'₃}
  {F₁₃ : C'₁ ⥤ C'₃} {p₁ : C₁ ⥤ C'₁} {p₂ : C₂ ⥤ C'₂} {p₃ : C₃ ⥤ C'₃}
  {LE₁₂ : D₁ ⥤ D₂} {LE₂₃ : D₂ ⥤ D₃} {LE₁₃ : D₁ ⥤ D₃} {LF₁₂ : D'₁ ⥤ D'₂} {LF₂₃ : D'₂ ⥤ D'₃}
  {LF₁₃ : D'₁ ⥤ D'₃} {Lp₁ : D₁ ⥤ D'₁} {Lp₂ : D₂ ⥤ D'₂} {Lp₃ : D₃ ⥤ D'₃}

/-- **Transitivity of squares of left derived functors.** Let `Φᵢⱼ : LEᵢⱼ ⋙ Lpⱼ ⟶ Lpᵢ ⋙ LFᵢⱼ`
be induced by underived squares `eᵢⱼ` through the counits, and `τ : LE₁₂ ⋙ LE₂₃ ⟶ LE₁₃`,
`τ' : LF₁₂ ⋙ LF₂₃ ⟶ LF₁₃` by underived comparisons `c`, `c'`. If the underived squares are
compatible with `c` and `c'`, so are the derived ones with `τ` and `τ'`, provided `Lp₁ ⋙ LF₁₃`
is a left derived functor of `p₁ ⋙ F₁₃` (for the counit `γ`). -/
lemma leftDerived_square_trans (W : MorphismProperty C₁)
    [Q₁.IsLocalization W]
    (αE₁₂ : Q₁ ⋙ LE₁₂ ⟶ E₁₂ ⋙ Q₂) (αE₂₃ : Q₂ ⋙ LE₂₃ ⟶ E₂₃ ⋙ Q₃) (αE₁₃ : Q₁ ⋙ LE₁₃ ⟶ E₁₃ ⋙ Q₃)
    (αF₁₂ : Q'₁ ⋙ LF₁₂ ⟶ F₁₂ ⋙ Q'₂) (αF₂₃ : Q'₂ ⋙ LF₂₃ ⟶ F₂₃ ⋙ Q'₃)
    (αF₁₃ : Q'₁ ⋙ LF₁₃ ⟶ F₁₃ ⋙ Q'₃)
    (αp₁ : Q₁ ⋙ Lp₁ ⟶ p₁ ⋙ Q'₁) (αp₂ : Q₂ ⋙ Lp₂ ⟶ p₂ ⋙ Q'₂) (αp₃ : Q₃ ⋙ Lp₃ ⟶ p₃ ⋙ Q'₃)
    (γ : Q₁ ⋙ Lp₁ ⋙ LF₁₃ ⟶ p₁ ⋙ F₁₃ ⋙ Q'₃)
    (hγ : γ = (whiskerRight αp₁ LF₁₃ ≫ whiskerLeft p₁ αF₁₃ :
      Q₁ ⋙ Lp₁ ⋙ LF₁₃ ⟶ p₁ ⋙ F₁₃ ⋙ Q'₃))
    [(Lp₁ ⋙ LF₁₃).IsLeftDerivedFunctor γ W]
    (τ : LE₁₂ ⋙ LE₂₃ ⟶ LE₁₃) (c : E₁₂ ⋙ E₂₃ ⟶ E₁₃)
    (hτ : ∀ K, τ.app (Q₁.obj K) ≫ αE₁₃.app K =
      LE₂₃.map (αE₁₂.app K) ≫ αE₂₃.app (E₁₂.obj K) ≫ Q₃.map (c.app K))
    (τ' : LF₁₂ ⋙ LF₂₃ ⟶ LF₁₃) (c' : F₁₂ ⋙ F₂₃ ⟶ F₁₃)
    (hτ' : ∀ K, τ'.app (Q'₁.obj K) ≫ αF₁₃.app K =
      LF₂₃.map (αF₁₂.app K) ≫ αF₂₃.app (F₁₂.obj K) ≫ Q'₃.map (c'.app K))
    (Φ₁₂ : LE₁₂ ⋙ Lp₂ ⟶ Lp₁ ⋙ LF₁₂) (e₁₂ : E₁₂ ⋙ p₂ ⟶ p₁ ⋙ F₁₂)
    (hΦ₁₂ : ∀ K, Φ₁₂.app (Q₁.obj K) ≫ LF₁₂.map (αp₁.app K) ≫ αF₁₂.app (p₁.obj K) =
      Lp₂.map (αE₁₂.app K) ≫ αp₂.app (E₁₂.obj K) ≫ Q'₂.map (e₁₂.app K))
    (Φ₂₃ : LE₂₃ ⋙ Lp₃ ⟶ Lp₂ ⋙ LF₂₃) (e₂₃ : E₂₃ ⋙ p₃ ⟶ p₂ ⋙ F₂₃)
    (hΦ₂₃ : ∀ K, Φ₂₃.app (Q₂.obj K) ≫ LF₂₃.map (αp₂.app K) ≫ αF₂₃.app (p₂.obj K) =
      Lp₃.map (αE₂₃.app K) ≫ αp₃.app (E₂₃.obj K) ≫ Q'₃.map (e₂₃.app K))
    (Φ₁₃ : LE₁₃ ⋙ Lp₃ ⟶ Lp₁ ⋙ LF₁₃) (e₁₃ : E₁₃ ⋙ p₃ ⟶ p₁ ⋙ F₁₃)
    (hΦ₁₃ : ∀ K, Φ₁₃.app (Q₁.obj K) ≫ LF₁₃.map (αp₁.app K) ≫ αF₁₃.app (p₁.obj K) =
      Lp₃.map (αE₁₃.app K) ≫ αp₃.app (E₁₃.obj K) ≫ Q'₃.map (e₁₃.app K))
    (h : ∀ K, p₃.map (c.app K) ≫ e₁₃.app K =
      e₂₃.app (E₁₂.obj K) ≫ F₂₃.map (e₁₂.app K) ≫ c'.app (p₁.obj K)) :
    whiskerRight τ Lp₃ ≫ Φ₁₃ =
      (associator _ _ _).hom ≫ whiskerLeft LE₁₂ Φ₂₃ ≫ (associator _ _ _).inv ≫
        whiskerRight Φ₁₂ LF₂₃ ≫ (associator _ _ _).hom ≫ whiskerLeft Lp₁ τ' := by
  subst hγ
  apply Functor.leftDerived_ext (LF := Lp₁ ⋙ LF₁₃) (W := W)
    (α := (whiskerRight αp₁ LF₁₃ ≫ whiskerLeft p₁ αF₁₃ :
      Q₁ ⋙ Lp₁ ⋙ LF₁₃ ⟶ p₁ ⋙ F₁₃ ⋙ Q'₃))
  ext K
  have h₁ := αp₃.naturality (c.app K)
  have h₂ := τ'.naturality (αp₁.app K)
  have h₃ := αF₂₃.naturality (e₁₂.app K)
  have h₄ := Φ₂₃.naturality (αE₁₂.app K)
  have h₅ := congrArg LF₂₃.map (hΦ₁₂ K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp] at h₁ h₂ h₃ h₄ h₅
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]
  rw [hΦ₁₃ K, ← Lp₃.map_comp_assoc, hτ K]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, ← Q'₃.map_comp, h K, ← reassoc_of% h₂, hτ' (p₁.obj K), reassoc_of% h₅,
    reassoc_of% h₃, ← reassoc_of% h₄, reassoc_of% (hΦ₂₃ (E₁₂.obj K))]
  simp only [Functor.map_comp]

section HomotopyCategory

variable {ι : Type*} {c : ComplexShape ι} {V₁ V₂ V₃ W₁ W₂ W₃ : Type*} [Category* V₁]
  [Category* V₂] [Category* V₃] [Category* W₁] [Category* W₂] [Category* W₃] [Preadditive V₁]
  [Preadditive V₂] [Preadditive V₃] [Preadditive W₁] [Preadditive W₂] [Preadditive W₃]
  {E₁₂ : V₁ ⥤ V₂} {E₂₃ : V₂ ⥤ V₃} {E₁₃ : V₁ ⥤ V₃} {F₁₂ : W₁ ⥤ W₂} {F₂₃ : W₂ ⥤ W₃}
  {F₁₃ : W₁ ⥤ W₃} {p₁ : V₁ ⥤ W₁} {p₂ : V₂ ⥤ W₂} {p₃ : V₃ ⥤ W₃}
  [E₁₂.Additive] [E₂₃.Additive] [E₁₃.Additive] [F₁₂.Additive] [F₂₃.Additive] [F₁₃.Additive]
  [p₁.Additive] [p₂.Additive] [p₃.Additive]

/-- The compatibility of squares `eᵢⱼ : Eᵢⱼ ⋙ pⱼ ⟶ pᵢ ⋙ Fᵢⱼ` with comparisons
`c : E₁₂ ⋙ E₂₃ ⟶ E₁₃` and `c' : F₁₂ ⋙ F₂₃ ⟶ F₁₃` passes to the induced transformations of
functors between homotopy categories. -/
lemma mapHomotopyCategory_square_trans (e₁₂ : E₁₂ ⋙ p₂ ⟶ p₁ ⋙ F₁₂)
    (e₂₃ : E₂₃ ⋙ p₃ ⟶ p₂ ⋙ F₂₃) (e₁₃ : E₁₃ ⋙ p₃ ⟶ p₁ ⋙ F₁₃) (κ : E₁₂ ⋙ E₂₃ ⟶ E₁₃)
    (κ' : F₁₂ ⋙ F₂₃ ⟶ F₁₃)
    (h : ∀ X, p₃.map (κ.app X) ≫ e₁₃.app X =
      e₂₃.app (E₁₂.obj X) ≫ F₂₃.map (e₁₂.app X) ≫ κ'.app (p₁.obj X))
    (e₁₂H : E₁₂.mapHomotopyCategory c ⋙ p₂.mapHomotopyCategory c ⟶
      p₁.mapHomotopyCategory c ⋙ F₁₂.mapHomotopyCategory c)
    (e₂₃H : E₂₃.mapHomotopyCategory c ⋙ p₃.mapHomotopyCategory c ⟶
      p₂.mapHomotopyCategory c ⋙ F₂₃.mapHomotopyCategory c)
    (e₁₃H : E₁₃.mapHomotopyCategory c ⋙ p₃.mapHomotopyCategory c ⟶
      p₁.mapHomotopyCategory c ⋙ F₁₃.mapHomotopyCategory c)
    (κH : E₁₂.mapHomotopyCategory c ⋙ E₂₃.mapHomotopyCategory c ⟶ E₁₃.mapHomotopyCategory c)
    (κ'H : F₁₂.mapHomotopyCategory c ⋙ F₂₃.mapHomotopyCategory c ⟶ F₁₃.mapHomotopyCategory c)
    (he₁₂H : ∀ C, e₁₂H.app ((HomotopyCategory.quotient V₁ c).obj C) =
      (HomotopyCategory.quotient W₂ c).map ((NatTrans.mapHomologicalComplex e₁₂ c).app C))
    (he₂₃H : ∀ C, e₂₃H.app ((HomotopyCategory.quotient V₂ c).obj C) =
      (HomotopyCategory.quotient W₃ c).map ((NatTrans.mapHomologicalComplex e₂₃ c).app C))
    (he₁₃H : ∀ C, e₁₃H.app ((HomotopyCategory.quotient V₁ c).obj C) =
      (HomotopyCategory.quotient W₃ c).map ((NatTrans.mapHomologicalComplex e₁₃ c).app C))
    (hκH : ∀ C, κH.app ((HomotopyCategory.quotient V₁ c).obj C) =
      (HomotopyCategory.quotient V₃ c).map ((NatTrans.mapHomologicalComplex κ c).app C))
    (hκ'H : ∀ C, κ'H.app ((HomotopyCategory.quotient W₁ c).obj C) =
      (HomotopyCategory.quotient W₃ c).map ((NatTrans.mapHomologicalComplex κ' c).app C))
    (K : HomotopyCategory V₁ c) :
    (p₃.mapHomotopyCategory c).map (κH.app K) ≫ e₁₃H.app K =
      e₂₃H.app ((E₁₂.mapHomotopyCategory c).obj K) ≫
        (F₂₃.mapHomotopyCategory c).map (e₁₂H.app K) ≫
        κ'H.app ((p₁.mapHomotopyCategory c).obj K) := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [hκH, he₁₃H, he₁₂H]
  erw [he₂₃H ((E₁₂.mapHomologicalComplex c).obj C), hκ'H ((p₁.mapHomologicalComplex c).obj C)]
  simp only [Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact h (C.X n)

end HomotopyCategory

end CategoryTheory.Functor
