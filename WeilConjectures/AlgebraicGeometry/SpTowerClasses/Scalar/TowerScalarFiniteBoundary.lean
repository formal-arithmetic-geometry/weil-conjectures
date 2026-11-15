/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarFiniteBoundaryData
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.ScalarFiniteBoundaryEquality

/-! # Finite evaluation of scalar extension of an arbitrary integral arrow -/

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

/-- Scalar extension and finite evaluation preserve the underlying integral arrow. -/
private theorem finiteBoundaryEquality_of_composition {D : Type u} [Category D]
    {X X' Y Y' : D} (q : X ⟶ X') (r : Y ⟶ Y')
    {a : X' ⟶ Y'} {beta : X ⟶ Y}
    (h : q ≫ a = beta ≫ r) : finiteBoundaryEquality q r a beta := by
  exact ⟨a, beta, HEq.rfl, HEq.rfl, h⟩

theorem scalarFiniteBoundary (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (hc : unitNormalization c.scalar.T
      (SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T))
      c.scalar.adjunction c.scalarUnit (scalarGenerator l E T))
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :
    ScalarFiniteBoundary l E c f n := by
  refine ⟨?_⟩
  dsimp [ScalarFiniteBoundary]
  exact finiteBoundaryEquality_of_composition _ _
    (scalarFiniteBoundary_composition l E c hc f n)

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
