/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernFinite
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernIntegralProjection
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernNormalizedBoundary
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceIntegralKummerComparison
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison

/-! # Reduction of a local completed Chern class
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit
  HasDerivedCategory.standard Etale.projectiveLineTraceDatum
  Scheme.finiteEtaleTateLine

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

namespace UniformizerChernNormalizationData

/-- The finite factor has the normalized finite Kummer specification. -/
-- The normalization hypothesis hz retains the repair of the former missing hypothesis.
theorem localChern_transport_finite_spec
    {s : UniformizerChernNormalizationData l Y}
    {z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧}
    {k : LocalFiniteArrow l Y s}
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z)
    (hk : LocalComposite l Y s z = FiniteComparison l Y s k) :
    LocalFiniteChernSpecCanonical l Y s k := by
  unfold LocalFiniteChernSpecCanonical LocalFiniteChernSpec
  apply (Etale.ordinaryFiniteP1ChernSpec_iff _ _ _ _ _ _).mpr
  apply (comparison_mapExt_bijective AddCommGrpCat.{u + 1} (ProjectiveLine Y)
    _ _ 2).injective
  apply (DiagonalTrace.finiteExtEndpointEquiv
    (SpTowerClasses.integerComparison (ProjectiveLine Y))
    ((forgetComparisonIso (ULift.{u + 1} (completedResidue l s.E s.π s.n))
      (ProjectiveLine Y)).app (Scheme.finiteEtaleTateLine (ProjectiveLine Y)
        (l ^ (s.n + 1)) (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.hA))).injective
  exact (localChern_transport_integral_projection l Y hk).trans
    ((localChern_normalized_integral_boundary l Y hz).trans
      (DiagonalTrace.diagonalTrace_integralKummer_comparison l
        (ProjectiveLine Y) (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA
        s.tq.chernX.kummer
        (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow)
        (SpTowerClasses.hyperplanePic Y)))

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
