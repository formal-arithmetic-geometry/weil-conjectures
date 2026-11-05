/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalFiniteCoverLocalZero
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Testing categorical sheaf epimorphisms by local lifts on finite covers

Source: Stacks Project, Tags 00W1, 00W9 and 00WL, expressed using coefficient
epimorphisms and exact filtered colimits rather than underlying elements.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

set_option backward.isDefEq.respectTransparency false

variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  (J : GrothendieckTopology C) [HasSheafify J A]
  [∀ V : C, HasFiniteProducts (Over V)]

end CategoryTheory.Sheaf
