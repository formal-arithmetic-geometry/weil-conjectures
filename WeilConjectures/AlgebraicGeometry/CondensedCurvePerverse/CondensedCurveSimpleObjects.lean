/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurvePerverseStatement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.CategoryTheory.Simple

import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpenNormal
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
import WeilConjectures.WeilSheaf.DenseOpen
import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.ConstructibleSheaf.NormalOpenLowerStar
import WeilConjectures.ConstructibleSheaf.DenseOpenUnitNormal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.ProperBaseChange.NormalRingFieldExtensionDescent
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.AlgebraicGeometry.SixFunctors.StratificationGenericNeighborhood
import WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends
import WeilConjectures.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity
import WeilConjectures.Mathlib.Topology.Sober
import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.CategoryTheory.Triangulated.TStructure.CohomologyComparisonPasting
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Limits.Creates
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneralStatement
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCurveLisseDescent
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Regular

/-! # Simple objects of the condensed curve perverse hearts

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-curve-simples/_section.md,
with prop-a1-curve-perverse-simples.proof.md in that directory.
(blueprint: sk-lem-wft-curve-simples).

Both hearts are the recorded geometric heart and its Frobenius-pair heart. Ordinary
middle extension uses the actual module direct image. In the Weil case its structure
is transported by the canonical base-change isomorphism. Irreducibility of a lisse
object is simplicity within the lisse full subcategory, not among all module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverse

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Canonical placement of a Weil module in degree zero followed by shift n.
The structure is the exact inverse-image/single-complex comparison followed by the
canonical shift comparison. No structure isomorphism is chosen.
Source: latest blueprint, sk-lem-wft-curve-simples, degree-zero and shifted objects
(blueprint: sk-lem-wft-curve-simples). -/
def weilPlaced {C : Scheme.{u}} (g : C ≅ C) (n : ℤ) :
    WeilConjectures.condensedWeilModules Λ g.hom ⥤
      Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ g.hom).mapDerivedCategory :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (Functor.associator (DerivedCategory.singleFunctor _ 0) (shiftFunctor _ n)
        (CondensedRing.upperStar Λ g.hom).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
        ((CondensedRing.upperStar Λ g.hom).mapDerivedCategory.commShiftIso n) ≪≫
      (Functor.associator (DerivedCategory.singleFunctor _ 0)
        (CondensedRing.upperStar Λ g.hom).mapDerivedCategory (shiftFunctor _ n)).symm ≪≫
      Functor.isoWhiskerRight
        ((CondensedRing.upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0)
        (shiftFunctor _ n) ≪≫
      Functor.associator (CondensedRing.upperStar Λ g.hom)
        (DerivedCategory.singleFunctor _ 0) (shiftFunctor _ n))

end AlgebraicGeometry.ProEtale.CondensedCurvePerverse
