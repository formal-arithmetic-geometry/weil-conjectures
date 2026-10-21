/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Pasting forward left-coefficient tensor actions

Source: the agent-formulated categorical pasting calculation for Stacks Project,
Tags 0B56 (equation-projection-formula-map) and 0GL1 (lemma-j-shriek-and-tensor),
`sites-cohomology.tex`, over the projection arrow in main-20261015
`sk-prop-cohsm.proof.md`, (G13) (blueprint: lem-pur-composite-left-projection-action).
The abstract assertion is the node's formal calculation, not a claim of either Stacks tag.

## Main definitions and statements

- `CategoryTheory.compositeLeftProjectionAction`: the specified pasted map.
- `CategoryTheory.compositeLeftProjectionAction_coherence`: joint naturality and the unit
  and associativity equations for that map.
-/

@[expose] public section

set_option autoImplicit false

universe u₀ v₀ u₁ v₁ u₂ v₂

open CategoryTheory MonoidalCategory

namespace CategoryTheory

/-- The specified composite `t B (J M) ≫ R.map (v (F B) M)`.
Source: agent-formulated pasting of Stacks Tags 0B56 and 0GL1, over the projection arrow
in main-20261015 `sk-prop-cohsm.proof.md`, (G13).
(blueprint: lem-pur-composite-left-projection-action) -/
def compositeLeftProjectionAction
    {C₀ : Type u₀} [Category.{v₀} C₀] [MonoidalCategory C₀]
    {C₁ : Type u₁} [Category.{v₁} C₁] [MonoidalCategory C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [MonoidalCategory C₂]
    (F : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂) (R : C₁ ⥤ C₀) (J : C₂ ⥤ C₁)
    (t : ∀ (B : C₀) (N : C₁), B ⊗ R.obj N ⟶ R.obj (F.obj B ⊗ N))
    (v : ∀ (C : C₁) (M : C₂), C ⊗ J.obj M ⟶ J.obj (Q.obj C ⊗ M))
    (B : C₀) (M : C₂) : B ⊗ (J ⋙ R).obj M ⟶ (J ⋙ R).obj ((F ⋙ Q).obj B ⊗ M) :=
  t B (J.obj M) ≫ R.map (v (F.obj B) M)

/-- Pasting the two given forward actions preserves joint naturality, the unit equation
and the coefficient-associativity equation. `f.εIso.inv` and `(f.μIso B B').inv` are
`e_F` and `δ^F`; similarly for `q`. The composite comparisons are explicitly
`Q.map f.εIso.inv ≫ q.εIso.inv` and `Q.map (f.μIso B B').inv ≫
(q.μIso (F.obj B) (F.obj B')).inv`.

Source: agent-formulated categorical pasting for Stacks Tags 0B56 and 0GL1,
`sites-cohomology.tex`, over main-20261015 `sk-prop-cohsm.proof.md`, (G13).
(blueprint: lem-pur-composite-left-projection-action)

Proof plan, following the seven elementary steps of the node:
1. Expand the two composite inverse comparisons. Tensor bifunctoriality gives
   `h^S = (Q(e_F) tensor 1) ≫ h^Q` and
   `a^S = (Q(δ^F) tensor 1) ≫ a^Q`.
2. For coefficient and object morphisms, apply naturality of `v` and then of `t`;
   functoriality of `R` gives joint naturality of the specified composite.
3. Apply naturality of `v` at `e_F`, then the unit law of `v`, then that of `t`.
   Keep `F(1)` distinct from the unit object throughout.
4. For associativity, apply naturality of `v` at `δ^F` to the expanded left side.
5. Apply the associativity law of `v`; combine the adjacent associator and `δ^F`
   factors into `a^F` under `R`.
6. Apply the associativity law of `t` at `(B,B',J M)`.
7. Apply naturality of `t` at `v (F B') M`. The adjacent outer factors are the
   composite at `(B, Q(F B') tensor M)`; tensor bifunctoriality combines the inner
   two factors into `1 tensor T`. This is the required associativity equation.
Only the functor and tensor laws of the two dependency definitions are used. -/
theorem compositeLeftProjectionAction_coherence
    {C₀ : Type u₀} [Category.{v₀} C₀] [MonoidalCategory C₀]
    {C₁ : Type u₁} [Category.{v₁} C₁] [MonoidalCategory C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [MonoidalCategory C₂]
    (F : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂) (R : C₁ ⥤ C₀) (J : C₂ ⥤ C₁)
    (f : F.CoreMonoidal) (q : Q.CoreMonoidal)
    (t : ∀ (B : C₀) (N : C₁), B ⊗ R.obj N ⟶ R.obj (F.obj B ⊗ N))
    (v : ∀ (C : C₁) (M : C₂), C ⊗ J.obj M ⟶ J.obj (Q.obj C ⊗ M))
    (ht : ∀ (B B' : C₀) (N N' : C₁) (b : B ⟶ B') (n : N ⟶ N'),
      t B N ≫ R.map (F.map b ⊗ₘ n) = (b ⊗ₘ R.map n) ≫ t B' N')
    (hv : ∀ (C C' : C₁) (M M' : C₂) (c : C ⟶ C') (m : M ⟶ M'),
      v C M ≫ J.map (Q.map c ⊗ₘ m) = (c ⊗ₘ J.map m) ≫ v C' M')
    (ht_unit : ∀ N : C₁,
      t (𝟙_ C₀) N ≫ R.map (f.εIso.inv ▷ N ≫ (λ_ N).hom) = (λ_ (R.obj N)).hom)
    (hv_unit : ∀ M : C₂,
      v (𝟙_ C₁) M ≫ J.map (q.εIso.inv ▷ M ≫ (λ_ M).hom) = (λ_ (J.obj M)).hom)
    (ht_assoc : ∀ (B B' : C₀) (N : C₁),
      t (B ⊗ B') N ≫
          R.map ((f.μIso B B').inv ▷ N ≫ (α_ (F.obj B) (F.obj B') N).hom) =
        (α_ B B' (R.obj N)).hom ≫ B ◁ t B' N ≫ t B (F.obj B' ⊗ N))
    (hv_assoc : ∀ (C C' : C₁) (M : C₂),
      v (C ⊗ C') M ≫
          J.map ((q.μIso C C').inv ▷ M ≫ (α_ (Q.obj C) (Q.obj C') M).hom) =
        (α_ C C' (J.obj M)).hom ≫ C ◁ v C' M ≫ v C (Q.obj C' ⊗ M)) :
    (∀ (B B' : C₀) (M M' : C₂) (b : B ⟶ B') (m : M ⟶ M'),
      compositeLeftProjectionAction F Q R J t v B M ≫
          (J ⋙ R).map ((F ⋙ Q).map b ⊗ₘ m) =
        (b ⊗ₘ (J ⋙ R).map m) ≫ compositeLeftProjectionAction F Q R J t v B' M') ∧
    (∀ M : C₂,
      compositeLeftProjectionAction F Q R J t v (𝟙_ C₀) M ≫
          (J ⋙ R).map ((Q.map f.εIso.inv ≫ q.εIso.inv) ▷ M ≫ (λ_ M).hom) =
        (λ_ ((J ⋙ R).obj M)).hom) ∧
    (∀ (B B' : C₀) (M : C₂),
      compositeLeftProjectionAction F Q R J t v (B ⊗ B') M ≫
          (J ⋙ R).map
            ((Q.map (f.μIso B B').inv ≫ (q.μIso (F.obj B) (F.obj B')).inv) ▷ M ≫
              (α_ ((F ⋙ Q).obj B) ((F ⋙ Q).obj B') M).hom) =
        (α_ B B' ((J ⋙ R).obj M)).hom ≫
          B ◁ compositeLeftProjectionAction F Q R J t v B' M ≫
          compositeLeftProjectionAction F Q R J t v B ((F ⋙ Q).obj B' ⊗ M)) := by
  sorry

end CategoryTheory
