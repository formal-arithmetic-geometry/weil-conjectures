/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # A braided comparison through a K-flat localization

Source: Stacks Project, Tags 06YS and 06YT; uniqueness of derived bifunctors.

(blueprint: lem-pur-u2-normalized-braided-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category MonoidalCategory
open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal

namespace CategoryTheory

variable {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory D] [MonoidalCategory E]
  [BraidedCategory A] [BraidedCategory B] [BraidedCategory D] [BraidedCategory E]
  (Q : A ⥤ D) (L : B ⥤ E) (F : A ⥤ B) (G : D ⥤ E)
  [Q.LaxBraided] [L.LaxBraided] [F.Braided] (e : Q ⋙ G ≅ F ⋙ L)

end CategoryTheory
