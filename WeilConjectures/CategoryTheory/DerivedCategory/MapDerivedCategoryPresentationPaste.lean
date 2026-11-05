/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation

/-! # Pasted squares of presented derived functors

Two pasting identities of natural isomorphisms between presented derived functors follow
from the corresponding identities of the represented ordinary natural isomorphisms.

Source: Stacks Project, Tag 05RU (universal property of localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

open DerivedPresentation

section Paste

variable {A₀ A₁ B₀ B₁ C₀ C₁ E : Type*}
  [Category A₀] [Category A₁] [Category B₀] [Category B₁] [Category C₀] [Category C₁]
  [Category E]
  [Abelian A₀] [Abelian A₁] [Abelian B₀] [Abelian B₁] [Abelian C₀] [Abelian C₁] [Abelian E]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory B₀]
  [HasDerivedCategory B₁] [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory E]

end Paste

section Lift

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

end Lift

end CategoryTheory.Functor
