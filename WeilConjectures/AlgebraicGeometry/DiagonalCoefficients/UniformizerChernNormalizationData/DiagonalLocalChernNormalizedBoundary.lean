/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalChernNormalizedBoundaryProjection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalChernNormalizedBoundaryKummer

/-! # Finite boundary of a normalized completed Chern arrow -/

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
namespace UniformizerChernNormalizationData

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory HasDerivedCategory.standard
  Scheme.finiteEtaleTateLine

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

/-- The integral finite projection of a normalized completed Chern arrow is the
positive Kummer composite. No scalar-extension functor or supplied finite factor occurs. -/
theorem localChern_normalized_integral_boundary
    {s : UniformizerChernNormalizationData l Y}
    {z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧}
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z) :
    completedIntegralProjection l (ProjectiveLine Y)
      (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA
      (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow) z =
    DiagonalTrace.evaluatedIntegralKummerClass l (ProjectiveLine Y)
      (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA s.tq.chernX.kummer
      (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow)
      (SpTowerClasses.hyperplanePic Y) := by
  exact (DiagonalTrace.localChern_normalized_boundary_projection l (ProjectiveLine Y)
    s.tq.chernX s.tq.restrictionX s.tq.coefficientsX _ s.n s.hA
    (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow) s.tq.LX _ z
    (by simpa only [LocalNormalized] using hz)).trans
      (DiagonalTrace.localChern_normalized_boundary_kummer l (ProjectiveLine Y)
        s.tq.chernX s.tq.restrictionX s.tq.coefficientsX _ s.n s.hA
        (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow)
        s.tq.finiteX (SpTowerClasses.hyperplanePic Y))

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
