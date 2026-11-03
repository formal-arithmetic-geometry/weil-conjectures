/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralAffineCoefficientCounit.GeneralAffineCoefficientCounitNormalizationDefs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Affine.AffineDualizingCoefficient
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.AffineCoefficientCounit.AffineCoefficientCounitMaps
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitSuccessor
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessComparison
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunction
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineCounitTensor
public import WeilConjectures.AlgebraicGeometry.CurrentProEtaleProjectionFormulaStatement
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
public import WeilConjectures.AlgebraicGeometry.FiniteCompactificationTranspose.FiniteRingCompactificationTransposeComparison
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
public import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteTensorProjection
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleOrderedIntegration
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorIntegrationSiteComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTateCoordinates
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace

/-! Kummer-normalized exponent independence for the general affine coefficient counit.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/lem-pur-projection-purity-agreement.proof.md,
common maximum exponent comparison (blueprint: lem-pur-affine-coefficient-counit-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
open AffineOrderedIntegrationGeneral FiniteCompactificationTranspose
variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The complete common-maximum Kummer comparison, separated from the main theorem.

Proof: compare both annihilating powers with their maximum. The power maps on roots
and on the middle multiplicative sheaf give the kernel equation and generator equation;
the finite Tate pullback theorem makes the induced line map canonical. Naturality of
projective trace, open restriction, coefficient-first counits, and the specified Hom
transpose gives the remaining four equalities. Power-map composition supplies the
cocycle, including equal exponents and the zero-ring case.
-/
theorem general_affine_exponent_independence
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) (hell : ell.Prime) (_hp : (ringChar k).Prime)
    (hne : ringChar k ≠ ell) {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (r s : ℕ) (_hrs : r ≤ s)
    (hA : ((ell ^ (r + 1) : ℕ) : A) = 0)
    (hA' : ((ell ^ (s + 1) : ℕ) : A) = 0)
    (H : E A Y)
    (_hH : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y H) :
    letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
    let N := ell ^ (r + 1)
    let M := ell ^ (s + 1)
    let hN : 0 < N := pow_pos hell.pos _
    let hM : 0 < M := pow_pos hell.pos _
    let hY := baseUnit k ell hell hne (r + 1) aY
    let hY' := baseUnit k ell hell hne (s + 1) aY
    ∃ (q : (ProjectiveLine Y).rootsOfUnitySheaf M ⟶
        (ProjectiveLine Y).rootsOfUnitySheaf N)
      (e : Scheme.finiteEtaleTateLine (ProjectiveLine Y) M A hA' ≅
        Scheme.finiteEtaleTateLine (ProjectiveLine Y) N A hA),
      q ≫ kernel.ι (N • 𝟙 (ProjectiveLine Y).gmSheaf) =
        (M / N) • kernel.ι (M • 𝟙 (ProjectiveLine Y).gmSheaf) ∧
      (∀ (U : (ProjectiveLine Y).Etaleᵒᵖ) (a : A)
        (z : ((ProjectiveLine Y).rootsOfUnitySheaf M).obj.obj U),
        e.hom.hom.app U (Scheme.finiteEtaleTateOneGenerator A M (ProjectiveLine Y)
          hA' U a z) = Scheme.finiteEtaleTateOneGenerator A N (ProjectiveLine Y)
            hA U a (q.hom.app U z)) ∧
      (Etale.ordinaryFinitePushforward A (ProjectiveLine Y ↘ Y)).map
          (projectiveExponentIso A Y e).hom ≫ Etale.ordinaryFiniteProjectiveLineTrace N hN A hA Y hY =
        Etale.ordinaryFiniteProjectiveLineTrace M hM A hA' Y hY' ∧
      (Etale.affineTraceLineLeft A Y).map (lineExponentIso A Y e).hom ≫
          CoordinateLine.integration A N hA Y hN hY =
        CoordinateLine.integration A M hA' Y hM hY' ∧
      (Etale.affineTraceLineLeft A Y).map (sourceExponentIso A Y e H).hom ≫
          (CoordinateLine.adjunction A N hA Y hN hY).counit.app H =
        (CoordinateLine.adjunction A M hA' Y hM hY').counit.app H ∧
      (C A Y).map ((Etale.affineTraceLineLeft A Y).map
          (sourceExponentIso A Y e H).hom) ≫
          (C A Y).map ((CoordinateLine.adjunction A N hA Y hN hY).counit.app H) =
        (C A Y).map ((CoordinateLine.adjunction A M hA' Y hM hY').counit.app H) ∧
      (C A (AffineSpace PUnit.{u + 1} Y)).map (sourceExponentIso A Y e H).hom ≫
          (C A (AffineSpace PUnit.{u + 1} Y)).map
            ((CoordinateLine.comparison A N hA Y hN hY).hom.app H) =
        (C A (AffineSpace PUnit.{u + 1} Y)).map
          ((CoordinateLine.comparison A M hA' Y hM hY').hom.app H) := by
  sorry

end AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
