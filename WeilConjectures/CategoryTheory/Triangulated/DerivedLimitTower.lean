/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor

import WeilConjectures.CategoryTheory.Triangulated.PBCDerivedLimitTowerCone
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerProperty

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The inverse limit of a K-injective tower represents its triangulated derived limit.
Source: Stacks Project, Derived Categories, Tags 0BK6, 0BK7 and 070M. -/
theorem derivedCategory_towerLimit_core
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (hP : HasCountableProducts (DerivedCategory A)) :
    letI : HasCountableProducts (DerivedCategory A) := hP
    ∀ (_ : EnoughInjectives A)
      (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
      (K : ℕ → DerivedCategory A) (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (_e : I.asFunctor ⋙ DerivedCategory.Q ≅ Functor.ofOpSequence f),
      ∃ c : Cone I.asFunctor, Nonempty (IsLimit c) ∧
        IsDerivedLimit f (DerivedCategory.Q.obj c.pt) := by
  let : HasCountableProducts (DerivedCategory A) := hP
  intro hI I hKI K f e
  have hc' := (derivedCategory_towerLimit_cone A) I
  obtain ⟨c, hc⟩ := hc'
  refine ⟨c, hc, ?_⟩
  exact (derivedCategory_towerLimit_property A hP hI I K f e c hc.some)

end CategoryTheory
