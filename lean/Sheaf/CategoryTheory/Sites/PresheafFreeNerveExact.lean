/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.AlgebraicTopology.SetCechNerveFreeResolution
import Sheaf.CategoryTheory.Sites.PresheafCechComplex

/-!
# Exactness of the free module presheaf nerve

Source: Stacks Project, Cohomology on Sites, Tags 03F5, 03AT; Hypercoverings, 01GC.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The alternating chain complex of free module presheaves on the Čech nerve.
Source: Stacks Project, Tags 03AS and 01GC.
(blueprint: lem-sc-presheaf-free-nerve-exact) -/
noncomputable def presheafFreeNerveComplex
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) : ChainComplex (PresheafOfModules.{v} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (f.cechNerve ⋙ PresheafOfModules.free R)

/-- Objectwise exactness of a complex of presheaf modules implies exactness.
Source: Mathlib categorical exactness of jointly conservative evaluations.
(blueprint: lem-sc-presheaf-free-nerve-exact-eval-glue)
Proof: kernels and cokernels in presheaf module categories are computed objectwise,
so the family of evaluation functors jointly reflects the zero homology condition. -/
theorem exactAt_of_presheaf_evaluations
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (K : ChainComplex (PresheafOfModules.{v} R) ℕ) (a : ℕ)
    (h : ∀ X : Cᵒᵖ, (((PresheafOfModules.evaluation R X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).ExactAt a) : K.ExactAt a := by
  sorry

/-- Objectwise exactness of the evaluated free nerve.
Source: Stacks Project, Tags 03F5 and 03AT.
The evaluated complex is identified with the set Cech free resolution.
(blueprint: lem-sc-presheaf-free-nerve-exact-eval)
-/
theorem presheafFreeNerveComplex_exactAt_eval
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (n : ℕ) (X : Cᵒᵖ) :
    (((PresheafOfModules.evaluation R X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (presheafFreeNerveComplex R f)).ExactAt (n + 1) := by
  sorry

theorem presheafFreeNerveComplex_exactAt
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (n : ℕ) :
    (presheafFreeNerveComplex R f).ExactAt (n + 1) := by
  apply exactAt_of_presheaf_evaluations R
  exact presheafFreeNerveComplex_exactAt_eval R f n

end CategoryTheory
