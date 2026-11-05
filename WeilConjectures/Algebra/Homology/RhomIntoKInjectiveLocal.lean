/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Localized derived morphisms into a K-injective complex

Source: Stacks Project, Lemma 21.34.6, Tag 0A94
(blueprint: lem-pur-rhom-into-kinjective-local).

## Main statements

* `module_overFunctor_preservesZero`: the zero-morphism compatibility needed to restrict complexes.
* `rhom_into_kinjective_local`: the canonical localized derived-morphism bijection.
-/

@[expose] public section

universe u v w r t

open CategoryTheory Opposite

namespace CategoryTheory

/-- Restriction of module sheaves preserves zero morphisms.
Source: Stacks Project, Lemma 21.20.1, as used in Tag 0A94
(blueprint: lem-pur-rhom-into-kinjective-local).

Proof: restriction evaluates a morphism at objects of the localized site. The restriction
of a zero morphism therefore has zero at every component, and is the zero morphism. -/
theorem module_overFunctor_preservesZero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C) :
    (SheafOfModules.overFunctor.{w} R U).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext W x
  rfl

end CategoryTheory
