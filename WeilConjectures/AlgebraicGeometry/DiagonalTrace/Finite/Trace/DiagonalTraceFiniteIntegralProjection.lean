/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceModelTraceComponents
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFinitePretraceComponents

/-! # A single finite projection of a completed diagonal integral
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor

/-- The completed diagonal integral induces the identity after one coefficient projection. -/
theorem diagonalTrace_finiteIntegralProjection
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ)
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (hf : f = pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ∨
      f = pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (t : Result l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f t.Rc)
    (n : ℕ) :
    (diagonalCompletedUnderlying l (ProjectiveLine Y)).map
        (a.hom ≫ t.Rc.R.map δ ≫ t.trace) ≫
      ((diagonalCompletedRestriction l (ProjectiveLine Y)).mapDerivedCategorySingleFunctor
        0).hom.app _ ≫
      (DerivedCategory.singleFunctor (DiagonalMod l (ProjectiveLine Y)) 0).map
        (t.coefficientsS.coefficientProjection.app (op n)) =
    ((diagonalCompletedRestriction l (ProjectiveLine Y)).mapDerivedCategorySingleFunctor
        0).hom.app _ ≫
      (DerivedCategory.singleFunctor (DiagonalMod l (ProjectiveLine Y)) 0).map
        (t.coefficientsS.coefficientProjection.app (op n)) := by
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  simpa only [Category.assoc] using
    (diagonalTrace_integral_of_components l t hP (a.hom ≫ t.Rc.R.map δ) n
      (diagonalTrace_finitePretrace_components l Y hY D δ hδ f hf t.toPresentation a n))

end AlgebraicGeometry.ProEtale.DiagonalTrace
