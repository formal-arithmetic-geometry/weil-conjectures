/-
Copyright (c) 2026 The Weil SHEAF project authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil SHEAF project authors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Counit normal form for two pasted mates

Source: blueprint `main-20261015`, `sec-six-functors-basics`,
`det-prop-scalar-six-direct-image.proof.md`, Formal properties and Finite rings paragraphs;
Stacks Project, categories.tex, Tags 001B, 001I and 0037.
(blueprint: lem-sfb-pasted-mates-counit-normalization)
-/

@[expose] public section

set_option autoImplicit false

universe u₀ u₁ u₂ u₃ u₄ u₅ v₀ v₁ v₂ v₃ v₄ v₅

namespace CategoryTheory

/-- The counit transpose of two successive right mates, with arbitrary input and output arrows.
Source: blueprint `main-20261015`, `det-prop-scalar-six-direct-image.proof.md`, Formal properties
(composition and counit compatibility of mates) and Finite rings (transport through `ν*`);
Stacks Project, categories.tex, Tags 001B, 001I and 0037.
(blueprint: lem-sfb-pasted-mates-counit-normalization)

Proof: Write `β₁ = mateEquiv adj₀ adj₁ α₁` and `β₂ = mateEquiv adj₁ adj₂ α₂`.
1. Expand `L₂` of the composite using functoriality. Naturality of `adj₂.counit` at `t`
   moves `L₂.map (R₂.map t)` past the counit, leaving `t` after the counit at `H₂(H₁(J))`.
2. Apply `mateEquiv_counit adj₁ adj₂ α₂ (H₁.obj J)`
   (blueprint lemma `lem-amb-mate-unit-counit`) to replace the transpose of `β₂` by
   `α₂` followed by `H₂` of the middle counit.
3. Naturality of `α₂` at `β₁.app J` moves `L₂(G₂(β₁.app J))` through `α₂`.
   Functoriality of `H₂` groups `L₁(β₁.app J)` with the middle counit.
4. Apply `mateEquiv_counit adj₀ adj₁ α₁ J` to that grouped composite, and expand `H₂`
   of the resulting composite. Associativity gives the displayed five factors. Both sides
   have source `L₂.obj Q` and target `K`; no exactness or invertibility is used. -/
theorem pasted_mates_counit_normalization
    {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
    {D₀ : Type u₃} {D₁ : Type u₄} {D₂ : Type u₅}
    [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
    [Category.{v₃} D₀] [Category.{v₄} D₁] [Category.{v₅} D₂]
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
    {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G₁ : C₀ ⥤ C₁} {G₂ : C₁ ⥤ C₂} {H₁ : D₀ ⥤ D₁} {H₂ : D₁ ⥤ D₂}
    (α₁ : G₁ ⋙ L₁ ⟶ L₀ ⋙ H₁) (α₂ : G₂ ⋙ L₂ ⟶ L₁ ⋙ H₂)
    (J : D₀) (Q : C₂) (K : D₂)
    (b : Q ⟶ G₂.obj (G₁.obj (R₀.obj J))) (t : H₂.obj (H₁.obj J) ⟶ K) :
    L₂.map (b ≫ G₂.map ((mateEquiv adj₀ adj₁ α₁).app J) ≫
      (mateEquiv adj₁ adj₂ α₂).app (H₁.obj J) ≫ R₂.map t) ≫ adj₂.counit.app K =
      L₂.map b ≫ α₂.app (G₁.obj (R₀.obj J)) ≫ H₂.map (α₁.app (R₀.obj J)) ≫
        H₂.map (H₁.map (adj₀.counit.app J)) ≫ t := by
  sorry

end CategoryTheory
