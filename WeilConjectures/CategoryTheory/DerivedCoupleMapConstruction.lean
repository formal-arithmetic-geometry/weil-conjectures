/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Construction of induced maps on images and cycle quotients

Source: Stacks Project, Lemma 12.21.2 (Tag 011R), Remark 12.21.5 (Tag 0AMJ).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {s : ℕ}

namespace DerivedCoupleMapData

variable {D E : ℤ → ℤ → C}
    {a : ∀ p q, D p q ⟶ D (p - 1) (q + 1)}
    {f : ∀ p q, E p q ⟶ D (p + 2) (q - 1)}
    {g : ∀ p q, D p q ⟶ E (p + s) (q - s)}
    {β : ∀ p q, E (p - s - 2) (q + s + 1) ⟶ E p q}
    {hβ : ∀ p q, β p q ≫ f p q ≫ g (p + 2) (q - 1) = 0}
    {hg : ∀ p q, g p q ≫ f (p + s) (q - s) = 0}

end DerivedCoupleMapData

end CategoryTheory
