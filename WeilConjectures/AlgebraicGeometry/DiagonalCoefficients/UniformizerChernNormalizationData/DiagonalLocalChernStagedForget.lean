/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralKummer
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRootLimitCompatibility
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFiniteRootsCanonicalMap
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernStageTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernStagedArrow

/-! # Forgetting coefficients in a staged local reduction
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the same abelian structure on module sheaves as the exact-derived comparison APIs.
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

namespace UniformizerChernNormalizationData

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory HasDerivedCategory.standard
  Scheme.finiteEtaleTateLine

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

/-- Forgetting all coefficient actions, the staged arrow is the completed arrow between the
underlying unit and line endpoint maps. -/
theorem localStagedArrow_forget (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor (DiagonalAb (ProjectiveLine Y)) 0).map
        (localUnitEndpoint l Y s) ≫
      SpTowerClasses.mapSingleArrow
        (cartierForget (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)) 2
        (localStagedArrow l Y s z) =
    SpTowerClasses.mapSingleArrow (localCompletedForget l (ProjectiveLine Y)) 2 z ≫
      ((DerivedCategory.singleFunctor (DiagonalAb (ProjectiveLine Y)) 0).map
        (localLineEndpoint l Y s))⟦(2 : ℤ)⟧' := by
  exact single_stage_trans _ _ _ _ _ _ _ _
    (mapSingleArrow_exact_stage s.completedP.F _ _
      (s.completedP.underlying ≪≫ localCompletedForgetIso l (ProjectiveLine Y))
      s.completedP.unitIso s.completedP.lineIso z)
    (single_stage_trans _ _ _ _ _ _ _ _
      (Endpoint.mapSingleArrow_forget _ (s.toIntegral.units (ProjectiveLine Y))
        s.toIntegral.lineP _)
      (Endpoint.mapSingleArrow_forget_exact _ (s.scalar.units (ProjectiveLine Y)) s.scalar.lineP
        s.eP.F _ s.eP.underlying s.eP.unitIso (s.lineP.iso l) _))

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
