/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralUnitReduction
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Normalized.NormalizedKummerTarget

/-! # Integral quotient reduction with its two normalized comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Simultaneous integral reduction identifies the integer source and Kummer target,
with the integer generator and the positive boundary fixing the two comparisons. -/
theorem exists_normalizedKummerReduction (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (k : Kummer l T) :
    (fun R : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} ↦
    ∃ (r : Reduction T R) (M : Systems T R)
      (i : r.forget.F.obj M ≅ roots l T)
      (a : r.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj (integers T)) ≅
        unit T R)
      (b : r.derived.obj (((DerivedCategory.singleFunctor (Ab T) 0).obj
        (units T))⟦(1 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor (Systems T R) 0).obj M)⟦(2 : ℤ)⟧),
      r.model.sourceNormalization a (integerGenerator T R r.forget) ∧
      r.model.targetNormalization (ShortComplex.mk k.inclusion k.power k.zero)
        k.exact b i) (Rrings l T) := by
  obtain ⟨r, a, ha⟩ := exists_integralUnitReduction T (Rrings l T)
  obtain ⟨M, i, b, hb⟩ := exists_normalizedKummerTarget l T hT k r
  exact ⟨r, M, i, a, b, ha, hb⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
