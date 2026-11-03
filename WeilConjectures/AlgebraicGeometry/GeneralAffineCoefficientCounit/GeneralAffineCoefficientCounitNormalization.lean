/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineCoefficientCounit.AffineCoefficientCounitNormalization
import WeilConjectures.AlgebraicGeometry.FiniteCompactificationTranspose.FiniteRingCompactificationTransposeComparison
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalAffineTrace.DiagonalAffineTraceCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
import WeilConjectures.SixFunctors.Etale.Derived.Identity
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
import WeilConjectures.AlgebraicGeometry.FiniteCompactificationTranspose.FiniteRingCompactificationTransposeComparison
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalAffineTrace.DiagonalAffineTraceCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
import WeilConjectures.SixFunctors.Etale.Derived.Identity
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegrationGeneral.AffineOrderedGeneralCounitNormalization
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.AlgebraicGeometry.CurrentProEtaleProjectionFormulaStatement
public import WeilConjectures.AlgebraicGeometry.TensorTraceTranspose
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.GeneralAffineCoefficientCounit.GeneralAffineCoefficientCounitNormalizationDefs
import WeilConjectures.AlgebraicGeometry.GeneralAffineCoefficientCounit.GeneralAffineCoefficientCounitDomains
import WeilConjectures.AlgebraicGeometry.GeneralAffineCoefficientCounit.GeneralAffineCoefficientCounitNormalizationDefs
import WeilConjectures.AlgebraicGeometry.GeneralAffineCoefficientCounit.GeneralAffineCoefficientExponentIndependence
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Affine.AffineDualizingCoefficient
public import WeilConjectures.AlgebraicGeometry.AffineCoefficientCounit.AffineCoefficientCounitMaps
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitSuccessor
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessComparison
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunction
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineCounitTensor
public import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
public import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteTensorProjection
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleOrderedIntegration
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorIntegrationSiteComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTateCoordinates
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace

/-! # Finite-ring affine coefficient counits

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md,
ordered affine integration and canonical reassociation
(blueprint: lem-pur-affine-coefficient-counit-normalization).

The generic domain predicates in AffineCoefficientCounitNormalization are reused. Unlike
its former specialized theorem, the statements here allow every finite commutative
ell-primary ring and either permitted base field. All morphisms below are specified
adjunction counits, coefficient-first projections, or their restricted site transposes.
Equalities in ordinary-origin coordinates are also stated after the actual comparison;
ProjectionLaw, TransposeLaw and RepresentativeLaw retain the canonical identifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
open AffineOrderedIntegrationGeneral FiniteCompactificationTranspose

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Independence of the annihilating exponent at fixed A. The transition is specified
by its roots-of-unity power equation and its value on every scalar/root generator;
there is no freely supplied source isomorphism. The equations retain the projective
trace, its open restriction, the actual ordinary counit, its site image, and its
exceptional transpose. Any two exponents compare through their maximum.
Source: latest blueprint, projection-purity agreement, common normalized integration
(blueprint: lem-pur-affine-coefficient-counit-normalization).

Proof:
1. For r≤s the Kummer diagrams have vertical maps z↦z^(ell^(s-r)) on roots and
on the middle G_m, and identity on the right G_m. Their connecting maps therefore
identify the O(1) Chern classes. The normalized finite Tate transition sends each
root tensor a to the corresponding powered root tensor a and is an isomorphism.
2. Both columns of the unit/Kummer decomposition of P1 correspond. Inverting that
decomposition identifies the second-projection traces in the first displayed equation.
3. Naturality of the open adjunction counit gives the restricted-trace equation.
The coefficient-first projections commute with the canonical tensor/source comparison;
substitute the tensor-trace counit formula to obtain the ordinary counit equation.
4. Apply C to that equality and use the actual B square. The restricted Hom transpose
and its naturality give the final Gamma equation, in its ordinary-origin coordinates.
Power maps compose and are identities at equal exponents. Hence the identifications
satisfy the cocycle condition; use max(r,s) for unordered pairs. This is independence
at fixed A, not a scalar-change assertion. The argument includes the zero ring.
-/
theorem affine_line_exponent_independence
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
  exact general_affine_exponent_independence A k _hk ell hell _hp hne aY r s _hrs hA hA' H _hH

end AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
