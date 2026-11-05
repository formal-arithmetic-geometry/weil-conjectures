/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Mates of derived adjunctions and coefficient comparisons

This file contains the abstract diagram chases behind the compatibility of the derived base
change map with the restriction of scalars along a morphism of coefficient rings.

Consider two adjunctions `G ⊣ F` and `G' ⊣ F'` (think: over the coefficients `Λ` and `Λ'`),
"restriction" functors `P₁`, `P₂` from the primed to the unprimed categories and a square
`θ : P₁ ⋙ G ⟶ G' ⋙ P₂` whose mate is `κ : F' ⋙ P₁ ⟶ P₂ ⋙ F`. Suppose that the adjunctions are
derived to adjunctions `LG ⊣ RF` and `LG' ⊣ RF'` along localization functors, with units and
counits computed in terms of those of `G ⊣ F` and `G' ⊣ F'` (as for `Adjunction.derived`), and
let `τ : DP₁ ⋙ LG ⟶ LG' ⋙ DP₂` and `σ : RF' ⋙ DP₁ ⟶ DP₂ ⋙ RF` be squares of derived functors
induced by `θ` and `κ`. Then `σ` is the mate of `τ`
(`CategoryTheory.Adjunction.mateEquiv_eq_of_isRightDerivedFunctor`).

Second, the mate of a square of left adjoints is compatible with restriction functors as
soon as the square and the adjunctions are (`CategoryTheory.Adjunction.mateEquiv_restrict`).
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Adjunction

section Components

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- The components of the mate of a square. -/
lemma mateEquiv_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (d : D) :
    (mateEquiv adj₁ adj₂ α).app d =
      adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (α.natTrans.app (R₁.obj d)) ≫
        R₂.map (H.map (adj₁.counit.app d)) := by
  simp [mateEquiv_apply]

end Components

section DerivedMate

variable {C₁ C₂ C₁' C₂' D₁ D₂ D₁' D₂' : Type*} [Category C₁] [Category C₂] [Category C₁']
  [Category C₂'] [Category D₁] [Category D₂] [Category D₁'] [Category D₂']
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} {G' : C₁' ⥤ C₂'} {F' : C₂' ⥤ C₁'}
  {P₁ : C₁' ⥤ C₁} {P₂ : C₂' ⥤ C₂}
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₁' : C₁' ⥤ D₁'} {L₂' : C₂' ⥤ D₂'}
  {LG : D₁ ⥤ D₂} {RF : D₂ ⥤ D₁} {LG' : D₁' ⥤ D₂'} {RF' : D₂' ⥤ D₁'}
  {DP₁ : D₁' ⥤ D₁} {DP₂ : D₂' ⥤ D₂}

/-- The mate of a square `τ` of derived left adjoints, precomposed with the image of the unit
`β'` of the primed right derived functor, in terms of the underived mate `κ` of the underived
square `θ` inducing `τ`. -/
lemma map_app_mateEquiv_app (adj : G ⊣ F) (adj' : G' ⊣ F') (θ : P₁ ⋙ G ⟶ G' ⋙ P₂)
    (κ : F' ⋙ P₁ ⟶ P₂ ⋙ F)
    (hθκ : ∀ N, P₁.map (adj'.unit.app N) ≫ κ.app (G'.obj N) =
      adj.unit.app (P₁.obj N) ≫ F.map (θ.app N))
    (dadj : LG ⊣ RF) (dadj' : LG' ⊣ RF') (α : L₁ ⋙ LG ⟶ G ⋙ L₂) (β : F ⋙ L₁ ⟶ L₂ ⋙ RF)
    (α' : L₁' ⋙ LG' ⟶ G' ⋙ L₂') (β' : F' ⋙ L₁' ⟶ L₂' ⋙ RF')
    (hη : ∀ X, dadj.unit.app (L₁.obj X) ≫ RF.map (α.app X) =
      L₁.map (adj.unit.app X) ≫ β.app (G.obj X))
    (hε' : ∀ X, LG'.map (β'.app X) ≫ dadj'.counit.app (L₂'.obj X) =
      α'.app (F'.obj X) ≫ L₂'.map (adj'.counit.app X))
    (φ₁ : L₁' ⋙ DP₁ ≅ P₁ ⋙ L₁) (φ₂ : L₂' ⋙ DP₂ ≅ P₂ ⋙ L₂) (τ : DP₁ ⋙ LG ⟶ LG' ⋙ DP₂)
    (hτ : ∀ N, τ.app (L₁'.obj N) ≫ DP₂.map (α'.app N) ≫ φ₂.hom.app (G'.obj N) =
      LG.map (φ₁.hom.app N) ≫ α.app (P₁.obj N) ≫ L₂.map (θ.app N)) (X : C₂') :
    DP₁.map (β'.app X) ≫ (mateEquiv dadj' dadj τ).app (L₂'.obj X) =
      φ₁.hom.app (F'.obj X) ≫ L₁.map (κ.app X) ≫ β.app (P₂.obj X) ≫
        RF.map (φ₂.inv.app X) := by
  have h₀ := dadj.unit.naturality (DP₁.map (β'.app X))
  have h₁ := τ.naturality (β'.app X)
  have h₂ := φ₂.inv.naturality (adj'.counit.app X)
  have h₃ := β.naturality (θ.app (F'.obj X) ≫ P₂.map (adj'.counit.app X))
  have h₄ := κ.naturality (adj'.counit.app X)
  have h₅ := dadj.unit.naturality (φ₁.hom.app (F'.obj X))
  have h₆ := hτ (F'.obj X)
  have h₇ := hη (P₁.obj (F'.obj X))
  have h₈ := hθκ (F'.obj X)
  have h₉ := adj'.right_triangle_components X
  have h₁₀ := hε' X
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₀ h₁ h₂ h₃
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₄ h₅ h₆ h₇
  simp only [Functor.comp_obj, Functor.id_obj] at h₈ h₉ h₁₀ ⊢
  have h₆' : τ.app (L₁'.obj (F'.obj X)) ≫ DP₂.map (α'.app (F'.obj X)) =
      LG.map (φ₁.hom.app (F'.obj X)) ≫ α.app (P₁.obj (F'.obj X)) ≫
        L₂.map (θ.app (F'.obj X)) ≫ φ₂.inv.app (G'.obj (F'.obj X)) := by
    rw [← cancel_mono (φ₂.hom.app (G'.obj (F'.obj X)))]
    simpa using h₆
  calc DP₁.map (β'.app X) ≫ (mateEquiv dadj' dadj τ).app (L₂'.obj X)
      = dadj.unit.app (DP₁.obj (L₁'.obj (F'.obj X))) ≫
          RF.map (τ.app (L₁'.obj (F'.obj X)) ≫ DP₂.map (α'.app (F'.obj X)) ≫
            DP₂.map (L₂'.map (adj'.counit.app X))) := by
        rw [mateEquiv_app, reassoc_of% h₀, ← RF.map_comp, ← RF.map_comp, reassoc_of% h₁,
          ← DP₂.map_comp, h₁₀, DP₂.map_comp]
    _ = dadj.unit.app (DP₁.obj (L₁'.obj (F'.obj X))) ≫
          RF.map (LG.map (φ₁.hom.app (F'.obj X)) ≫ α.app (P₁.obj (F'.obj X)) ≫
            L₂.map (θ.app (F'.obj X) ≫ P₂.map (adj'.counit.app X)) ≫ φ₂.inv.app X) := by
        rw [reassoc_of% h₆', ← h₂, L₂.map_comp, Category.assoc]
    _ = φ₁.hom.app (F'.obj X) ≫ L₁.map (adj.unit.app (P₁.obj (F'.obj X)) ≫
          F.map (θ.app (F'.obj X) ≫ P₂.map (adj'.counit.app X))) ≫ β.app (P₂.obj X) ≫
            RF.map (φ₂.inv.app X) := by
        rw [RF.map_comp, ← reassoc_of% h₅, RF.map_comp, reassoc_of% h₇, RF.map_comp,
          ← reassoc_of% h₃, L₁.map_comp, Category.assoc]
    _ = _ := by
        rw [F.map_comp, ← Category.assoc (adj.unit.app _), ← h₈, Category.assoc, ← h₄,
          ← P₁.map_comp_assoc, h₉, P₁.map_id, Category.id_comp]

/-- **Mates of derived adjunctions.** Let `LG ⊣ RF` and `LG' ⊣ RF'` be adjunctions whose unit
and counit are induced by those of `G ⊣ F` and `G' ⊣ F'` through the localization functors, and
let `τ : DP₁ ⋙ LG ⟶ LG' ⋙ DP₂` be induced by `θ : P₁ ⋙ G ⟶ G' ⋙ P₂`. If `RF' ⋙ DP₁` is a right
derived functor whose unit factors through `DP₁` of the unit `β'` of `RF'`, then any
`σ : RF' ⋙ DP₁ ⟶ DP₂ ⋙ RF` induced by the mate `κ` of `θ` is the mate of `τ`. -/
lemma mateEquiv_eq_of_isRightDerivedFunctor (adj : G ⊣ F) (adj' : G' ⊣ F')
    (θ : P₁ ⋙ G ⟶ G' ⋙ P₂) (κ : F' ⋙ P₁ ⟶ P₂ ⋙ F)
    (hθκ : ∀ N, P₁.map (adj'.unit.app N) ≫ κ.app (G'.obj N) =
      adj.unit.app (P₁.obj N) ≫ F.map (θ.app N))
    (dadj : LG ⊣ RF) (dadj' : LG' ⊣ RF') (α : L₁ ⋙ LG ⟶ G ⋙ L₂) (β : F ⋙ L₁ ⟶ L₂ ⋙ RF)
    (α' : L₁' ⋙ LG' ⟶ G' ⋙ L₂') (β' : F' ⋙ L₁' ⟶ L₂' ⋙ RF')
    (hη : ∀ X, dadj.unit.app (L₁.obj X) ≫ RF.map (α.app X) =
      L₁.map (adj.unit.app X) ≫ β.app (G.obj X))
    (hε' : ∀ X, LG'.map (β'.app X) ≫ dadj'.counit.app (L₂'.obj X) =
      α'.app (F'.obj X) ≫ L₂'.map (adj'.counit.app X))
    (φ₁ : L₁' ⋙ DP₁ ≅ P₁ ⋙ L₁) (φ₂ : L₂' ⋙ DP₂ ≅ P₂ ⋙ L₂) (τ : DP₁ ⋙ LG ⟶ LG' ⋙ DP₂)
    (hτ : ∀ N, τ.app (L₁'.obj N) ≫ DP₂.map (α'.app N) ≫ φ₂.hom.app (G'.obj N) =
      LG.map (φ₁.hom.app N) ≫ α.app (P₁.obj N) ≫ L₂.map (θ.app N))
    (W : MorphismProperty C₂') [L₂'.IsLocalization W] {H₀ : C₂' ⥤ D₁}
    (β'' : H₀ ⟶ L₂' ⋙ RF' ⋙ DP₁) [(RF' ⋙ DP₁).IsRightDerivedFunctor β'' W]
    (hβ'' : ∀ X, ∃ e, β''.app X = e ≫ DP₁.map (β'.app X)) (σ : RF' ⋙ DP₁ ⟶ DP₂ ⋙ RF)
    (hσ : ∀ X, DP₁.map (β'.app X) ≫ σ.app (L₂'.obj X) =
      φ₁.hom.app (F'.obj X) ≫ L₁.map (κ.app X) ≫ β.app (P₂.obj X) ≫
        RF.map (φ₂.inv.app X)) :
    mateEquiv dadj' dadj τ = σ := by
  refine (RF' ⋙ DP₁).rightDerived_ext β'' W _ _ _ (NatTrans.ext (funext fun X ↦ ?_))
  obtain ⟨e, he⟩ := hβ'' X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, he, Category.assoc]
  rw [map_app_mateEquiv_app adj adj' θ κ hθκ dadj dadj' α β α' β' hη hε' φ₁ φ₂ τ hτ X, hσ]

end DerivedMate

section Restrict

variable {AY AX AY' AX' BY BX BY' BX' : Type*} [Category AY] [Category AX] [Category AY']
  [Category AX'] [Category BY] [Category BX] [Category BY'] [Category BX']
  {Lf : AY ⥤ AX} {Rf : AX ⥤ AY} {Lf' : AY' ⥤ AX'} {Rf' : AX' ⥤ AY'}
  {Lg : AY ⥤ AY'} {Lg' : AX ⥤ AX'}
  {Mf : BY ⥤ BX} {Sf : BX ⥤ BY} {Mf' : BY' ⥤ BX'} {Sf' : BX' ⥤ BY'}
  {Mg : BY ⥤ BY'} {Mg' : BX ⥤ BX'}
  {rY : BY ⥤ AY} {rX : BX ⥤ AX} {rY' : BY' ⥤ AY'} {rX' : BX' ⥤ AX'}

end Restrict
section Counit

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
  {L : A ⥤ A'} {R : A' ⥤ A} {M : B ⥤ B'} {S : B' ⥤ B} {rA : B ⥤ A} {rA' : B' ⥤ A'}

end Counit

section Conjugate

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category B₁]
  [Category B₂] [Category B₃]
  {L₁ : A₂ ⥤ A₁} {R₁ : A₁ ⥤ A₂} {L₂ : A₃ ⥤ A₂} {R₂ : A₂ ⥤ A₃} {L : A₃ ⥤ A₁} {R : A₁ ⥤ A₃}
  {M₁ : B₂ ⥤ B₁} {S₁ : B₁ ⥤ B₂} {M₂ : B₃ ⥤ B₂} {S₂ : B₂ ⥤ B₃} {M : B₃ ⥤ B₁} {S : B₁ ⥤ B₃}
  {r₁ : B₁ ⥤ A₁} {r₂ : B₂ ⥤ A₂} {r₃ : B₃ ⥤ A₃}

end Conjugate
section Comparison

variable {AX Ac Ad AY BX Bc Bd BY : Type*} [Category AX] [Category Ac] [Category Ad]
  [Category AY] [Category BX] [Category Bc] [Category Bd] [Category BY]
  {Jc : AX ⥤ Ac} {Jd : AX ⥤ Ad} {Q : Ad ⥤ Ac} {Rq : Ac ⥤ Ad} {Rdg : Ad ⥤ AY} {Rcg : Ac ⥤ AY}
  {Jc' : BX ⥤ Bc} {Jd' : BX ⥤ Bd} {Q' : Bd ⥤ Bc} {Rq' : Bc ⥤ Bd} {Rdg' : Bd ⥤ BY}
  {Rcg' : Bc ⥤ BY} {rX : BX ⥤ AX} {rc : Bc ⥤ Ac} {rd : Bd ⥤ Ad} {rY : BY ⥤ AY}

end Comparison

end CategoryTheory.Adjunction
