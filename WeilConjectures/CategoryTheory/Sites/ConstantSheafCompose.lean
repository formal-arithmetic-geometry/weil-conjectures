/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Constant sheaves and change of coefficients

`CategoryTheory.constantSheafCompSheafComposeIso`: for a functor `F : A ⥤ B` preserving
sheafification, `F_*(M_C) ≅ (F M)_C` naturally in `M`. For instance `F = forget₂ (ModuleCat Λ) Ab`
on the pro-étale site (with `GrothendieckTopology.instPreservesSheafification`), identifying the
abelian sheaf underlying a constant sheaf of modules with a constant abelian sheaf.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {A B : Type*} [Category* A]
  [Category* B] (F : A ⥤ B) [HasWeakSheafify J A] [HasWeakSheafify J B] [J.HasSheafCompose F]
  [J.PreservesSheafification F]

end CategoryTheory
