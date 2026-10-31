/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.ScalarFiniteBoundarySquare

/-! # The scalar finite boundary equality with its prescribed endpoints -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
/-! Endpoint-witness reduction for the finite-boundary calculation.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`,
clause (2), endpoint transport and evaluation calculation.
(blueprint: lem-sfb-scalar-finite-boundary-composition-endpoints). -/
theorem scalarFiniteBoundary_boundaryEquality (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (hc : unitNormalization c.scalar.T
      (SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T))
      c.scalar.adjunction c.scalarUnit (scalarGenerator l E T))
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :
    finiteBoundaryEquality
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n))
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (finiteRootMap l E T n)⟦(2 : ℤ)⟧')
      (scalarFiniteBoundary_eval l E c f n)
      (scalarFiniteBoundary_integral l E c f n) := by
  exact ⟨_, _, HEq.rfl, HEq.rfl, scalarFiniteBoundary_composition l E c hc f n⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
