/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-!
# Blueprint statements

lem-weil-derived-limit-existence.
-/

@[expose] public section

universe t w v u

open CategoryTheory.Limits

namespace CategoryTheory

/-- Blueprint: lem-weil-derived-limit-existence. -/
theorem exists_isDerivedLimit_and_iso {D : Type u} [Category.{v} D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (K : ℕ → D) [HasProduct K] (f : ∀ n : ℕ, K (n + 1) ⟶ K n) :
    (∃ L : D, IsDerivedLimit f L) ∧
      ∀ (L L' : D), IsDerivedLimit f L → IsDerivedLimit f L' → Nonempty (L ≅ L') := by
  sorry

/-- Blueprint: lem-weil-derived-limit-existence. -/
theorem derivedCategory_countableProducts_and_towerLimit
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A] :
    ∃ hP : HasCountableProducts (DerivedCategory A),
      letI : HasCountableProducts (DerivedCategory A) := hP
      (∀ (J : Type t) [Countable J] (C : J → CochainComplex A ℤ),
        Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor C))))) ∧
      (∀ (J : Type t) [Countable J] (p : ℤ),
        PreservesLimitsOfShape (Discrete J) (DerivedCategory.homologyFunctor A p)) ∧
      (∀ (_ : EnoughInjectives A)
        (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
        (K : ℕ → DerivedCategory A) (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
        (_e : I.asFunctor ⋙ DerivedCategory.Q ≅ Functor.ofOpSequence f),
        ∃ c : Cone I.asFunctor, Nonempty (IsLimit c) ∧
          IsDerivedLimit f (DerivedCategory.Q.obj c.pt)) := by
  sorry

end CategoryTheory
