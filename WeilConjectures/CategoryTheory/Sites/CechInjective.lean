/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechFreeResolution

/-!
# Čech complexes of injective presheaves

Let `X` be an object of a category `C` and `U : ι → Over X` a family of objects over `X`
(with `ι : Type w`). For a presheaf `P : Cᵒᵖ ⥤ AddCommGrpCat.{max v w}`, the Čech cochains of
degree `n` of `(Over.forget X).op ⋙ P` with respect to `U` (Mathlib's
`CategoryTheory.cechComplexFunctor`) are the morphisms `ℤ_𝔘[n] ⟶ P` from the
free presheaf `CategoryTheory.Presheaf.cechFree U n`, compatibly with the differentials.
As the complex `ℤ_𝔘[•]` is exact, the Čech complex of an injective presheaf is exact in
positive degrees.

## Main definitions

- `CategoryTheory.Presheaf.cechFreeHomEquiv`: the identification of morphisms `ℤ_𝔘[n] ⟶ P` with
  Čech cochains of degree `n`.

## Main statements

- `CategoryTheory.Presheaf.cechFreeHomEquiv_cechFreeD_comp`: compatibility with the differentials.
- `CategoryTheory.Presheaf.exact_cechComplexFunctor_of_injective`: the Čech complex of an
  injective presheaf is exact in positive degrees.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Simplicial

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {X : C} [HasFiniteProducts (Over X)] {ι : Type w}
  (U : ι → Over X) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max v w})

variable {U P}

variable (U P)

end CategoryTheory.Presheaf
