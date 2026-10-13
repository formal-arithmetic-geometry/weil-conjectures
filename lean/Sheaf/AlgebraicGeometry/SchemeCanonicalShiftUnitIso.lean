/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift

/-! # Tensor with the translated unit

Source: Stacks Project, Tag 06YH, first-variable total tensor translation.
(blueprint: def-sc-scheme-canonical-shift-unit-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- The canonical comparison `𝟙[1] ⊗ K ≅ K[1]`, obtained by applying the first-variable
Koszul comparison and then translating the left unitor. It is an actual composite
of isomorphisms, with no choice of a resolution or of an existence witness.
Source: Stacks Project, Tag 06YH, total tensor translation.
(blueprint: def-sc-scheme-canonical-shift-unit-iso). -/
noncomputable def schemeCanonicalShiftUnitIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X) :
    (𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧ ⊗ K ≅ K⟦(1 : ℤ)⟧ := by
  letI := schemeCanonicalTensorShift X
  letI : (tensorRight K).CommShift ℤ :=
    Functor.CommShift₂.commShiftFlipObj (h := .int) K
  exact ((tensorRight K).commShiftIso (1 : ℤ)).app (𝟙_ (schemeDerivedCategory X)) ≪≫
    (shiftFunctor (schemeDerivedCategory X) (1 : ℤ)).mapIso (λ_ K)

end AlgebraicGeometry
