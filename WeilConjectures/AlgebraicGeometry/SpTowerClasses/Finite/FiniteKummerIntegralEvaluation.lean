/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralTowerBoundary
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralRootClass
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralLineClassEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralBoundaryEvaluationMap
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteComparedKummerBoundary

/-! # Evaluating the integral Kummer composite
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian constant

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- Evaluation of the integral tower Kummer class is the comparison image of the
etale Kummer class. Source: Stacks 03PL. -/
theorem finiteKummer_integral_evaluation (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ) (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (L : T.Pic) :
    finiteEvaluatedIntegralBoundary l T k n L =
      finiteIntegralRootClass l T n
        (T.kummerδ₁ (l ^ (n + 1)) hT (Scheme.Pic.toCohomologicalPicardGroup T L)) := by
  rw [finiteIntegralBoundary_evaluation_map, finiteIntegralLineClass_evaluation]
  exact finiteComparedKummerBoundary l T k n hT L

end AlgebraicGeometry.ProEtale.SpTowerClasses
