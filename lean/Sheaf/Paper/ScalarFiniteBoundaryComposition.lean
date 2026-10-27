/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Paper.TowerScalarFiniteBoundaryData

/-! # Scalar finite boundary composition identity -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The scalar evaluation morphism used in the finite boundary composite. -/
def scalarFiniteBoundary_eval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :=
  forgetEvaluatedArrow (SpTowerShriek.ev l E T n) (finiteForget l E T n)
    (lineEvaluation l E c n) (scalarChernArrow l E c f)

/-- The integral evaluation morphism used in the finite boundary composite. -/
def scalarFiniteBoundary_integral (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :=
  mapSingleArrow (abEvaluation T n) (2 : ℤ) (underlyingChernArrow l c f)


/--
The evaluated scalar arrow and the underlying integral arrow have the same finite
boundary composite. This is the composition identity used to construct the
`Fact` in `scalarFiniteBoundary`.

Source: blueprint latest,
`sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
evaluation and scalar-extension calculation.
(blueprint: lem-sfb-scalar-finite-boundary-composition).

Proof: transpose the scalar-extended arrow through the derived scalar adjunction.
On a K-flat representative, naturality of the universal scalar counit cancels the
resolution comparison and identifies the transpose with the ordinary scalar unit.
The normalization equation for the scalar unit then makes the source generator
scalarGenerator. Apply exact evaluation and restriction of scalars. The section,
restriction, and morphism equations of the specified forgetful functor identify
these evaluations with the displayed maps. The integer generator composite sends
k to k times one, so uniqueness of finiteQuotient fixes the source endpoint; the
pure-tensor equation for lineEvaluation sends z to one tensor z, so uniqueness of
finiteRootMap fixes the target endpoint. Naturality of the shifted single
comparisons transports the equality to degree two, yielding the displayed
composition identity. Empty schemes and zero arrows satisfy the same formulas.
-/
theorem scalarFiniteBoundary_composition (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (hc : unitNormalization c.scalar.T
      (SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T))
      c.scalar.adjunction c.scalarUnit (scalarGenerator l E T))
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n) ≫
        scalarFiniteBoundary_eval l E c f n =
      scalarFiniteBoundary_integral l E c f n ≫
        (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (finiteRootMap l E T n)⟦(2 : ℤ)⟧' := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
