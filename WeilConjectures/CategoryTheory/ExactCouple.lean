/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact

import WeilConjectures.CategoryTheory.DerivedCoupleMapExactness

/-!
# Bigraded exact couples and their spectral sequences

Source: Stacks Project, Homological Algebra, Definitions 12.21.1 and 12.21.3,
Lemma 12.21.2 and Remark 12.21.5 (Tags 011Q, 011S, 011R, 0AMJ), in the
bigraded convention of the blueprint (blueprint: def-sp-exact-couple).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

namespace BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C] {s : ℕ}

end BigradedExactCouple
end CategoryTheory
