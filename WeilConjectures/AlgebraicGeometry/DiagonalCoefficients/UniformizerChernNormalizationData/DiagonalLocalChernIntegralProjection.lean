/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison

/-! # Integral comparison for a local uniformizer reduction -/

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

/-- The integral image of a scalar-reduced arrow is its actual finite root projection.
This concerns every completed arrow, without any Chern or Kummer hypothesis. -/
theorem localChern_transport_integral_projection
    {s : UniformizerChernNormalizationData l Y}
    {z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧}
    {k : LocalFiniteArrow l Y s}
    (hk : LocalComposite l Y s z = FiniteComparison l Y s k) :
    Ext.mk₀CompMk₀ (SpTowerClasses.integerComparison (ProjectiveLine Y)).inv
      ((Etale.ordinaryFiniteClass
        (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)
        (Scheme.finiteEtaleTateLine (ProjectiveLine Y) (l ^ (s.n + 1))
          (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.hA) 2
          (LocalFiniteArrow.toHom l Y s k)).mapExactFunctor
        (comparisonUpperStar AddCommGrpCat.{u + 1} (ProjectiveLine Y)))
      ((forgetComparisonIso (ULift.{u + 1} (completedResidue l s.E s.π s.n))
        (ProjectiveLine Y)).hom.app (Scheme.finiteEtaleTateLine (ProjectiveLine Y)
          (l ^ (s.n + 1)) (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.hA)) =
    completedIntegralProjection l (ProjectiveLine Y)
      (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA
      (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow) z := by
  sorry

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
