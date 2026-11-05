/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp

/-! # Normalization of pasted descent squares -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {A₀ A₁ A₂ W₀ W₁ W₂ C₀ C₁ C₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category W₀] [Category W₁] [Category W₂]
  [Category C₀] [Category C₁] [Category C₂]
  {L₁ : A₀ ⥤ A₁} {L₂ : A₁ ⥤ A₂}
  {T₀ : A₀ ⥤ W₀} {T₁ : A₁ ⥤ W₁} {T₂ : A₂ ⥤ W₂}
  {U₀ : W₀ ⥤ C₀} {U₁ : W₁ ⥤ C₁} {U₂ : W₂ ⥤ C₂}
  {P₀ : A₀ ⥤ C₀} {P₁ : A₁ ⥤ C₁} {P₂ : A₂ ⥤ C₂}
  {R₁ : C₀ ⥤ C₁} {R₂ : C₁ ⥤ C₂}
  {RW₁ : W₀ ⥤ W₁} {RW₂ : W₁ ⥤ W₂}

end CategoryTheory.Functor
