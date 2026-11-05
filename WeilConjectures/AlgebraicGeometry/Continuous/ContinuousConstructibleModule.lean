/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
public import WeilConjectures.AlgebraicGeometry.LatticeClassDescent
public import WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
public import WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
public import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
public import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
public import WeilConjectures.AlgebraicGeometry.LatticePairDescentData
public import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
public import WeilConjectures.AlgebraicGeometry.LatticeCosetMap
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.LargeSetSheafification
public import WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
public import WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
public import WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
public import WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
public import Mathlib.Topology.Algebra.OpenSubgroup
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.CompactOpen
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification

/-!
# Constructible modules over continuous coefficient sheaves

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definitions 6.8.1 and 6.8.10
(blueprint: def-weil-pbc-continuous-constructible-module).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
