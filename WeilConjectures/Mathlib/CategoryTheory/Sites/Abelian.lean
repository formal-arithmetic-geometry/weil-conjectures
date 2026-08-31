/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linearity of sheafification

For an `R`-linear preadditive category `D`, the category `Sheaf J D` is `R`-linear (this
holds by instances, as sheaves form a full subcategory of presheaves), and the
sheafification functor `presheafToSheaf J D` is `R`-linear, being the left adjoint of the
(componentwise, hence `R`-linear) inclusion `sheafToPresheaf J D`. This is the `R`-linear
analogue of `CategoryTheory.presheafToSheaf_additive`.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (R : Type*) [Semiring R]
  {D : Type w} [Category.{w'} D] [Preadditive D] [Linear R D]
  {J : GrothendieckTopology C} [HasSheafify J D]

example : Linear R (Sheaf J D) := inferInstance

example : (sheafToPresheaf J D).Linear R := inferInstance

instance presheafToSheaf_linear : (presheafToSheaf J D).Linear R :=
  (sheafificationAdjunction J D).left_adjoint_linear

end CategoryTheory
