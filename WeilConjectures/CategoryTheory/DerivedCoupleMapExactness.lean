/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCoupleMapConstruction
import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Exactness of the induced maps on images and cycle quotients

Source: Stacks Project, Lemma 12.21.2 (Tag 011R), Remark 12.21.5 (Tag 0AMJ).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {s : ℕ}

-- The first chase: lift through f, lift to cycles, then pass to the quotient.

-- The second chase: lift a quotient class to cycles, then lift through g.

-- The third chase: subtract an incoming boundary before lifting through alpha.

end CategoryTheory
