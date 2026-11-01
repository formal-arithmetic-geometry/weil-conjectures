/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-! # Projection naturality used by the reduced theta mate -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory

/-- The projection identity used in the reduced theta calculation.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 3
(blueprint: lem-pur-finite-reduction-theta-factor-projection).

Proof: this is the right-variable naturality theorem for the projection tensor
map.  The reduced projection square `det-prop-sf-pf-reduction` supplies the
specialized `hπ`; after specialization, the displayed identity is exactly the
transport of that square through the inverse projection comparison.  Keeping
the categorical identity here makes the source and target explicit and avoids
silently treating the projection map as an equality.
-/
theorem finiteReduction_thetaFactor_projection_identity
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R)
    (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N))
    [∀ M N, IsIso (π M N)]
    (hπ : ∀ (M : C) {N N' : D} (φ : N ⟶ N'),
      L.obj M ◁ φ ≫ π M N' = π M N ≫ L.map (M ◁ F.map φ))
    (M : D) {N N' : D} (φ : N ⟶ N') :
    R.obj M ◁ F.map φ ≫ adj.projectionTensorMap π M N' =
      adj.projectionTensorMap π M N ≫ R.map (M ◁ φ) := by
  exact CategoryTheory.Adjunction.projectionTensorMap_naturality_right
    (adj := adj) (π := π) hπ M φ
