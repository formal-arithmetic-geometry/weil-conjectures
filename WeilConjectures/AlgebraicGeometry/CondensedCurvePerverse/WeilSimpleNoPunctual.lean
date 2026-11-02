/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurvePerverseStatement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.CategoryTheory.Simple
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpenNormal
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.WeilSheaf.DenseOpen
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.ConstructibleSheaf.NormalOpenLowerStar
public import WeilConjectures.ConstructibleSheaf.DenseOpenUnitNormal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.RingTheory.ProperBaseChange.NormalRingFieldExtensionDescent
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.CondensedWeilDenseLisseOpen
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.CohomologyComparisonPasting
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import Mathlib.CategoryTheory.Limits.Creates
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneralStatement
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.SixFunctors.StratificationGenericNeighborhood
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCurveLisseDescent
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Regular

/-! Punctual exclusion for condensed Weil middle extensions. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverse

/-- A Weil middle extension has no nonzero punctual equivariant subobject or quotient.
Source: latest blueprint, sk-lem-wft-curve-simples, proof steps (4) and (8).
(blueprint: sk-lem-wft-curve-simples). -/
theorem weil_simple_no_punctual (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (C₀ : Over (Spec (.of D.k₀))) [Smooth C₀.hom] [QuasiCompact C₀.hom]
    [IsSeparated C₀.hom] (_hPure : C₀.left.IsPureDimension 1) :
    ∀ P : WeilHeart (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius C₀),
      IsWeilSimpleMiddle D ell C₀ P.obj →
      ∀ Q : WeilHeart (Profinite.padicAlgClRingObj ell)
        (D.geometricFrobenius C₀),
        IsPunctualPerverse (Profinite.padicAlgClRingObj ell)
          (D.geometricFiber C₀).left Q.obj.carrier →
        (∀ f : Q ⟶ P, Mono f → IsZero Q) ∧
          (∀ f : P ⟶ Q, Epi f → IsZero Q) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCurvePerverse
