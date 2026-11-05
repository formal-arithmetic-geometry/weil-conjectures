/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.Sites.CechComplex
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Positive Čech exactness of injective categorical presheaves

Source: Stacks Project, Tag 03AW; the cofree contraction works in any abelian
coefficient category with the indicated products.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

set_option backward.isDefEq.respectTransparency false

variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A] [HasProducts.{u + 1} A] [HasProducts.{0} A]
  (P : Cᵒᵖ ⥤ A)

variable {V : C} [HasFiniteProducts (Over V)] {n : ℕ} (U : Fin n → Over V)

end CategoryTheory.Presheaf
