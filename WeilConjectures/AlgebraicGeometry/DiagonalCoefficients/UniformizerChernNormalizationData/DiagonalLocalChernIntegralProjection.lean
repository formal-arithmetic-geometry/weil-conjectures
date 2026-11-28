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
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernFiniteImage
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernStagedForget
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernEndpoints

/-! # Integral comparison for a local uniformizer reduction

The ordinary finite class of a finite arrow whose comparison image is the local composite of a
completed arrow `z` agrees, after forgetting coefficients, with the integral root projection of
`z`.

## Implementation details

The local composite is rewritten as a staged arrow (`localStagedArrow`). Each of the four
coefficient changes is transported to underlying abelian sheaves: exact realizations by
`mapSingleArrow_exact_stage`, derived scalar extensions by `Endpoint.mapSingleArrow_forget`
(using the adjoint normalization of the endpoints). The composite unit and line endpoint maps are
then identified with the integer generator and the root projection followed by the root map.
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

/-- The integer generator followed by the forgotten staged arrow is the completed integral
projection. -/
theorem localStagedArrow_integral (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor (DiagonalAb (ProjectiveLine Y)) 0).map
        ((SpTowerClasses.integerComparison (ProjectiveLine Y)).inv ≫
          (comparisonUpperStar AddCommGrpCat.{u + 1} (ProjectiveLine Y)).map
            (Etale.ordinaryFiniteIntegralGenerator
              (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)) ≫
          (forgetComparisonIso (ULift.{u + 1} (completedResidue l s.E s.π s.n))
            (ProjectiveLine Y)).hom.app (Etale.ordinaryFiniteConstant
              (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)) ≫
          (cartierForget (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)).map
            (DiagonalTrace.finiteEtaleConstantIso
              (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)).hom) ≫
      SpTowerClasses.mapSingleArrow
        (cartierForget (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)) 2
        (localStagedArrow l Y s z) =
    (completedIntegralProjection l (ProjectiveLine Y)
      (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA
      (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow) z).hom := by
  unfold completedIntegralProjection
  exact (shifted_glue _ _ _ _ _ _ _ _ (localUnitEndpoint_generator l Y s)
    (localStagedArrow_forget l Y s z) (localLineEndpoint_eq l Y s)).trans
    (Ext.homEquiv.apply_symm_apply _).symm

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
  apply Ext.ext
  have hAB := ordinaryFiniteClass_integral_hom (ULift.{u + 1} (completedResidue l s.E s.π s.n))
    (ProjectiveLine Y) (l ^ (s.n + 1)) s.hA (LocalFiniteArrow.toHom l Y s k)
  refine hAB.trans ?_
  have h₀ := localComposite_eq_staged l Y s z
  have h₁ := congrArg (fun t ↦
    (finiteUnitComparison (ULift.{u + 1} (completedResidue l s.E s.π s.n))
      (ProjectiveLine Y)).inv ≫ t ≫
        (finiteLineComparison (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (l ^ (s.n + 1))
          s.hA (ProjectiveLine Y)).hom) hk
  have h₂ := h₁.symm.trans h₀
  unfold FiniteComparison at h₂
  refine (congrArg (fun t ↦ _ ≫ SpTowerClasses.mapSingleArrow _ 2 t) h₂).trans ?_
  exact localStagedArrow_integral l Y s z

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
