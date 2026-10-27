/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!

# The exceptional exchange and external duality, abstractly

Let `f = p₁ : V ⟶ W` be a projection, with `f^*` (`L`, `L'`) and `f^!` (`R`, `R'`) on the generic
and special fibres, nearby cycles `S_V`, `S_W` (lax monoidal, with unit `σ = ε`), the pullback
exchange `α_f : f_s^* S_W ⟶ S_V f^*`, the exceptional exchange `β_f : S_V f^! ⟶ f_s^! S_W`, and the
projection-formula maps `t : f^! M ⊗ f^* N ⟶ f^!(M ⊗ N)`, `t'` on the special fibre. For the
external-duality maps `ξ : Q ⟶ f^! 𝟙`, `ξ' : Q' ⟶ f_s^! 𝟙` the normalized external-duality maps
are `κ_M = t(ξ ⊗ 1)` (followed by the unitor).

Blueprint `det-nearby-structural-product` derives its second equation (the *twisted case*)

`β_f S(κ_M) μ (a ⊗ α_f) = κ_{S M} (b ⊗ 1)`

from its first equation (the *constant case*) `β_f S(ξ) a = f_s^! σ ξ_s b`, from
`det-nearby-exceptional-tensor` (2) and from the unit law `μ (σ ⊗ 1) = 1`
(`CategoryTheory.exceptionalTwisted_of_constant`). Here `a : Q₀ ⟶ S_V Q` is `α_{p₂}` and
`b : Q₀ ⟶ Q'` is `p_{2s}^* θ`, on `Q₀ = p_{2s}^* S_X ω`.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory

variable {V V' W W' : Type*} [Category V] [Category V'] [Category W] [Category W']
  [MonoidalCategory V] [MonoidalCategory V'] [MonoidalCategory W] [MonoidalCategory W']
  {SV : V ⥤ V'} {SW : W ⥤ W'} [SV.LaxMonoidal] [SW.LaxMonoidal]
  {L : W ⥤ V} {R : W ⥤ V} {L' : W' ⥤ V'} {R' : W' ⥤ V'}

/-- **The twisted case of the exceptional exchange and external duality** (blueprint
`det-nearby-structural-product`, constant case ⇒ twisted case): with `κ_M = t(ξ ⊗ 1) ≫ R(λ)` and
`κ'_N = t'(ξ' ⊗ 1) ≫ R'(λ)`, the compatibility `hET` of `β` with the projection formula (blueprint
`det-nearby-exceptional-tensor` (2)), the naturality of `t'` in its first variable and the constant
case `hconst` give `(a ⊗ α) ≫ μ ≫ S_V(κ_M) ≫ β = (b ⊗ 1) ≫ κ'_{S_W M}`. -/
theorem exceptionalTwisted_of_constant (α : SW ⋙ L' ⟶ L ⋙ SV) (β : R ⋙ SV ⟶ SW ⋙ R')
    (t : ∀ M N : W, R.obj M ⊗ L.obj N ⟶ R.obj (M ⊗ N))
    (t' : ∀ M N : W', R'.obj M ⊗ L'.obj N ⟶ R'.obj (M ⊗ N))
    (ht' : ∀ {M M' : W'} (g : M ⟶ M') (N : W'),
      R'.map g ▷ L'.obj N ≫ t' M' N = t' M N ≫ R'.map (g ▷ N))
    (hET : ∀ M N : W, SV.obj (R.obj M) ◁ α.app N ≫ μ SV _ _ ≫ SV.map (t M N) ≫ β.app (M ⊗ N) =
      β.app M ▷ L'.obj (SW.obj N) ≫ t' _ _ ≫ R'.map (μ SW M N))
    {Q : V} {Q' Q₀ : V'} (ξ : Q ⟶ R.obj (𝟙_ W)) (ξ' : Q' ⟶ R'.obj (𝟙_ W'))
    (a : Q₀ ⟶ SV.obj Q) (b : Q₀ ⟶ Q')
    (hconst : a ≫ SV.map ξ ≫ β.app (𝟙_ W) = b ≫ ξ' ≫ R'.map (ε SW)) (M : W) :
    (a ⊗ₘ α.app M) ≫ μ SV _ _ ≫
        SV.map (ξ ▷ L.obj M ≫ t (𝟙_ W) M ≫ R.map (λ_ M).hom) ≫ β.app M =
      b ▷ L'.obj (SW.obj M) ≫ ξ' ▷ L'.obj (SW.obj M) ≫ t' (𝟙_ W') (SW.obj M) ≫
        R'.map (λ_ (SW.obj M)).hom := by
  have hβ := β.naturality (λ_ M).hom
  simp only [Functor.comp_map] at hβ
  have hET' := hET (𝟙_ W) M
  have hcon : (a ≫ SV.map ξ ≫ β.app (𝟙_ W)) ▷ L'.obj (SW.obj M) ≫
      t' (SW.obj (𝟙_ W)) (SW.obj M) ≫ R'.map (μ SW (𝟙_ W) M) ≫ R'.map (SW.map (λ_ M).hom) =
      b ▷ L'.obj (SW.obj M) ≫ ξ' ▷ L'.obj (SW.obj M) ≫ t' (𝟙_ W') (SW.obj M) ≫
        R'.map (λ_ (SW.obj M)).hom := by
    rw [hconst, comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
      reassoc_of% (ht' (ε SW) (SW.obj M)), ← R'.map_comp, ← R'.map_comp,
      Functor.LaxMonoidal.left_unitality]
  rw [← hcon, tensorHom_def, Category.assoc, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, hβ, ← Functor.LaxMonoidal.μ_natural_left_assoc]
  dsimp only [Functor.comp_obj]
  rw [whisker_exchange_assoc, reassoc_of% hET']
  simp only [comp_whiskerRight, Category.assoc]

end CategoryTheory
