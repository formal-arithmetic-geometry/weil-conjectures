/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.CategoryTheory.ExactCoupleConvergence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Functoriality of derived exact couples

Source: Stacks Project, Homological Algebra, Definitions 12.21.1 and 12.21.3,
Lemmas 12.21.2 and 12.21.4 (Tags 011Q, 011R, 011S, 011T)
(blueprint: lem-sp-derived-couple-functoriality).
-/

@[expose] public section

universe u v

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A degree-preserving morphism of type-`s` bigraded exact couples.
Source: Stacks Project, Homological Algebra, Definition 12.21.1, Tag 011Q
(blueprint: lem-sp-derived-couple-functoriality). -/
structure CoupleMorphism {s : ℕ} (X Y : BigradedExactCouple C s) where
  tD : ∀ p q : ℤ, X.D p q ⟶ Y.D p q
  tE : ∀ p q : ℤ, X.E p q ⟶ Y.E p q
  alpha_comm : ∀ p q : ℤ,
    tD p q ≫ Y.alpha p q = X.alpha p q ≫ tD (p - 1) (q + 1)
  f_comm : ∀ p q : ℤ,
    tE p q ≫ Y.f p q = X.f p q ≫ tD (p + 2) (q - 1)
  g_comm : ∀ p q : ℤ,
    tD p q ≫ Y.g p q = X.g p q ≫ tE (p + s) (q - s)



end CategoryTheory.BigradedExactCouple
