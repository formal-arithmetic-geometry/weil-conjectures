/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral

/-!
# Derived slice restriction with independent universes

Source: Stacks Project, Modules on Sites, Section 03DH (including Tag 03DJ);
Cohomology on Sites, Tag 08JB
(blueprint: def-weil-pbc-ringed-derived-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r m w w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The normalized comparison on the rank-one ring complex is the single-complex
comparison followed by the canonical localization factorization.
Source: Stacks 03DH and 08JB (blueprint: def-weil-pbc-ringed-derived-restriction). -/
def ringedDerivedRingRestrictionIsoGeneral (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (SheafOfModules.{r} R)]
    [HasDerivedCategory.{w'} (SheafOfModules.{r} (R.over U))] :
    (ringedDerivedRestrictionGeneral R U).obj
        ((HomologicalComplex.single _ (.up ℤ) 0 ⋙ DerivedCategory.Q).obj
          (SheafOfModules.unit R)) ≅
      (HomologicalComplex.single _ (.up ℤ) 0 ⋙ DerivedCategory.Q).obj
        (SheafOfModules.unit (R.over U)) :=
  haveI := (ringedOverFunctor_exactGeneral R U).1
  haveI := (ringedOverFunctor_exactGeneral R U).2.1
  haveI := (ringedOverFunctor_exactGeneral R U).2.2
  (SheafOfModules.overFunctor.{r} R U).mapDerivedCategorySingleFunctor 0 |>.app
    (SheafOfModules.unit R)

end CategoryTheory
