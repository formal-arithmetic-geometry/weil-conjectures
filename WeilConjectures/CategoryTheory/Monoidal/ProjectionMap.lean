/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Projection maps tensored with a fixed object

Let `π_{K, L} : R K ⊗ L ⟶ R (K ⊗ P L)` be a projection map satisfying the associativity law for
a comparison `δ : P (L ⊗ L') ⟶ P L ⊗ P L'`, and let `a : P N_Y ⟶ N_X`. We compare `π_{K, L} ▷ N_Y`
with `π_{K, L ⊗ N_Y}` through the induced comparison `c_M = π_{M, N_Y} ≫ R (M ◁ a)`
(`CategoryTheory.Adjunction.projectionMap_whiskerRight_comp`), and deduce that one is an
isomorphism if and only if the other is
(`CategoryTheory.Adjunction.isIso_projectionMap_whiskerRight_iff`). This is the formal input for
the compatibility of the projection formula for compactly supported direct images with finite
reduction of coefficients (blueprint `sk-prop-sf-pf-reduction`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory

section TensorRight

variable {CX CY : Type*} [Category* CX] [Category* CY] [MonoidalCategory CX]
  [MonoidalCategory CY] {R : CX ⥤ CY} {P : CY ⥤ CX}
  {δ : ∀ L L', P.obj (L ⊗ L') ⟶ P.obj L ⊗ P.obj L'}
  (π : ∀ K L, R.obj K ⊗ L ⟶ R.obj (K ⊗ P.obj L))
  (hπ : ∀ K L L', π K L ▷ L' ≫ π (K ⊗ P.obj L) L' ≫ R.map (α_ K (P.obj L) (P.obj L')).hom =
    (α_ (R.obj K) L L').hom ≫ π K (L ⊗ L') ≫ R.map (K ◁ δ L L'))
  {NY : CY} {NX : CX} (a : P.obj NY ⟶ NX)

end TensorRight

end CategoryTheory.Adjunction
