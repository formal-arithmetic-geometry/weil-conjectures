/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackCanonicalComparison

/-! # Canonical derived diagonal realization endpoint comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
/-- The canonical derived comparison has the prescribed shifted-line component. -/
theorem diagonalRealization_pullback_line_component
    (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian X] [IsNoetherian S]
    (coeff : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l)
    (hc : coeff.hom = diagonalCompletedCoefficientMap l f)
    (hX : IsUnit (l : Γ(X, ⊤))) (hS : IsUnit (l : Γ(S, ⊤)))
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (unit : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f coeff) :
    (diagonalRealization_pullback_canonical_comparison l f eX eS coeff hc).hom.app
      ((DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.shiftedLine l S) ≫ line.shift =
    eX.F.mapDerivedCategory.map
      (((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategory.commShiftIso (2 : ℤ)).app _
      ≪≫ (shiftFunctor (DerivedCategory (DiagonalCompleted l X)) (2 : ℤ)).mapIso
        ((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
          (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategorySingleFunctor 0 |>.app
            (Scheme.purTwistZlModule S l) |>.trans
              ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
                d.completedLine))).hom ≫
      eX.shiftedLine l X := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
