/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-! # Locally zero generalized sections of a presheaf with zero sheafification

Source: Stacks Project, Tags 00W1 and 00WB, expressed using exact filtered
colimits of local restriction kernels rather than underlying elements.
-/

@[expose] public section

universe u' u w v

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  (J : GrothendieckTopology C) [HasSheafify J A]
  [∀ V : C, HasFiniteProducts (Over V)]

end CategoryTheory.Presheaf
