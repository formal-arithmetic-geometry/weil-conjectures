/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct

/-! # The dual of the free coefficient telescope

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af.
-/

@[expose] public section

universe u w wSlice

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

section AbstractHom

variable {B : Type*} [Category B] [Abelian B]

end AbstractHom

section HomComplex

attribute [local irreducible] homComplexFunctor
  HomologicalComplex.single HomologicalComplex.singleObjXSelf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

private noncomputable abbrev modules :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

private noncomputable abbrev single := CochainComplex.singleFunctor (modules R) 0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency true in
end HomComplex

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency false in
end CategoryTheory
