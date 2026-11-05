/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence

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

end CategoryTheory.BigradedExactCouple
