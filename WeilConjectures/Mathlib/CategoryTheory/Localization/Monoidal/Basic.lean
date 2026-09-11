/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Monoidal classes of morphisms in a braided category

In a braided monoidal category, left and right whiskerings are conjugate by the braiding.
Consequently, a multiplicative class of morphisms which respects isomorphisms is monoidal as
soon as it is stable under left whiskering.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
  (W : MorphismProperty C)

/-- Alternative constructor for `MorphismProperty.IsMonoidal` in a braided monoidal category:
stability under left whiskering suffices, as the two whiskerings are related by the braiding

```text
          f ▷ Y
  X₁ ⊗ Y ────────→ X₂ ⊗ Y
     │                │
     │ β_ X₁ Y        │ β_ X₂ Y
     ↓                ↓
  Y ⊗ X₁ ────────→ Y ⊗ X₂
          Y ◁ f
```
-/
lemma IsMonoidal.mk_of_braided [W.IsMultiplicative] [W.RespectsIso]
    (h : ∀ (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂), W g → W (X ◁ g)) : W.IsMonoidal where
  whiskerLeft := h
  whiskerRight {X₁ X₂} f hf Y :=
    (W.arrow_mk_iso_iff (Arrow.isoMk (β_ X₁ Y) (β_ X₂ Y))).2 (h Y f hf)

end CategoryTheory.MorphismProperty
