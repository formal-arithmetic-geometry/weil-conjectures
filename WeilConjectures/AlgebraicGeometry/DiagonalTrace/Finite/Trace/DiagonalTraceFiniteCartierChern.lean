/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalTraceCompletedSupportedUnit

import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierChernStrict

/-! # Forgetting the support of the completed diagonal at one finite level -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap

/-- On the surface, forgetting support of the finite completed diagonal gives the
Chern arrow of the actual divisor line. The assertion precedes direct image
along a projection and the geometric adjunction. -/
theorem diagonalTrace_finiteCartierChern
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ)
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hn : c.Normalized l (ULift.{u} (Padic l)))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let U := diagonalCompletedUnderlying l (diagonalSurface Y)
    let V := r.F.mapDerivedCategory
    let ev := ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory
    U.map
        ((DerivedCategory.singleFunctor (DiagonalCompleted l (diagonalSurface Y)) 0).map
          (completedSupportedUnit l Y) ≫ δ) ≫
      shiftedComparison U (V ⋙ L.R) (k.lineMap l E L) 2 ≫ (L.projection n).app _ =
        (k.unitMap l E L ≫ (L.projection n).app _) ≫
          ev.map (V.map (SpTowerClasses.firstChern l E c
            (SpTowerClasses.diagonalPic Y))) := by
  suffices h : finiteChernEquation l Y c r k L n δ by
    dsimp only
    unfold finiteChernEquation completedBoundaryEquation finiteChernComposite at h
    dsimp only at h
    exact h
  rcases hδ with ⟨H, roots, a, b, xi, _ha, hxi, hfinite,
    L₀, _M, s, t, ⟨hs, ht, _hcompat⟩, hwhole⟩
  have hs' : SupportedSourceConeNormalization l Y D.ordinary s := by
    unfold SupportedSourceConeNormalization
    exact hs
  let presentation : ExtDerivedPresentation
      (D.ordinary.E.obj (diagonalIntegralSource Y)) H :=
    ⟨_, _, a, b, D.T.map (diagonalIntegralBoundary Y).hom⟩
  have hxi' : presentation.Presents xi := by
    unfold ExtDerivedPresentation.Presents ExtArrowPresentation
    exact hxi
  exact diagonalTrace_finiteCartierChern_strict l Y hY D.ordinary δ H roots xi hfinite
    s hs' t ht c hn hc r k presentation hxi' L₀ L n hwhole

end AlgebraicGeometry.ProEtale.DiagonalTrace
