/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Category.Grp.FilteredColimits

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

/-- Exactness of the existing slice module restriction, with independent sizes.
Source: Stacks, Modules on Sites, Section 03DH (localization of ringed sites)
(blueprint: def-weil-pbc-ringed-derived-restriction).
Proof: restriction evaluates on the objects of the slice, so preserves addition and
kernels. A covering of an object of the slice is exactly a covering of its underlying
object. Consequently local lifts of sections of an epimorphism remain local lifts
on the slice. Restriction therefore preserves cokernels, and is additive and exact.
The abelian exactness criterion gives preservation of finite limits and colimits. -/
theorem ringedOverFunctor_exactGeneral (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{m}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}] :
    (SheafOfModules.overFunctor.{m} R U).Additive ∧
      PreservesFiniteLimits (SheafOfModules.overFunctor.{m} R U) ∧
      PreservesFiniteColimits (SheafOfModules.overFunctor.{m} R U) := by
  sorry

/-- The functor on derived categories induced by the actual exact slice restriction.
Source: Stacks 03DH and 08JB (blueprint: def-weil-pbc-ringed-derived-restriction).
For commutative ring sheaves, apply this to their underlying ring sheaves. -/
def ringedDerivedRestrictionGeneral (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{m}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasDerivedCategory.{w} (SheafOfModules.{m} R)]
    [HasDerivedCategory.{w'} (SheafOfModules.{m} (R.over U))] :
    DerivedCategory (SheafOfModules.{m} R) ⥤
      DerivedCategory (SheafOfModules.{m} (R.over U)) :=
  haveI := (ringedOverFunctor_exactGeneral R U).1
  haveI := (ringedOverFunctor_exactGeneral R U).2.1
  haveI := (ringedOverFunctor_exactGeneral R U).2.2
  (SheafOfModules.overFunctor.{m} R U).mapDerivedCategory

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

/-- Slice restriction when the coefficient universe contains the site data. All
sheafification instances are supplied canonically, before elaborating its consumers.
Source: Stacks 03DH and 08JB (blueprint: def-weil-pbc-ringed-derived-restriction). -/
def ringedDerivedRestrictionSized {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (S : Sheaf J RingCat.{max u v}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{max u v} S)]
    [HasDerivedCategory.{w'} (SheafOfModules.{max u v} (S.over U))] :
    DerivedCategory (SheafOfModules.{max u v} S) ⥤
      DerivedCategory (SheafOfModules.{max u v} (S.over U)) :=
  ringedDerivedRestrictionGeneral.{u, v, max u v, max u v, w, w'} S U

end CategoryTheory
