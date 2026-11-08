/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Submission.WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.SixFunctors.Finite.BaseChange
import Submission.WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Submission.WeilConjectures.AlgebraicGeometry.Thickening
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Submission.WeilConjectures.AlgebraicGeometry.NoetherianApproximation
import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.FiniteStrata
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.ConstructibleSheaf.Refinement
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Submission.WeilConjectures.AlgebraicGeometry.NoetherNormalization
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.Topology.KrullDimension
import Submission.WeilConjectures.Mathlib.Topology.KrullDimension
import Submission.WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Fiber
import Submission.WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Defs.Filter
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Submission.WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension
import Submission.WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Submission.WeilConjectures.ProperBaseChange.MonicTensorPresentation.MonicTensorPresentation
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Submission.WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Submission.WeilConjectures.SixFunctors.BaseChange.Etale
import Submission.WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Submission.WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Submission.WeilConjectures.AlgebraicGeometry.DirectImageSplitCoverProduct
import Submission.WeilConjectures.ConstructibleSheaf.KernelCokernel
import Submission.WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSurjectivePullback
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Finite finitely presented pushforward preserves constructibility

Source: Stacks Project, Etale Cohomology, Tag 095R, lemma-finite-pushforward-constructible
(blueprint: lem-weil-pbc-finite-fp-pushforward-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem constructible_of_iso
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    (hF : IsConstructibleEtaleModuleSheaf F) : IsConstructibleEtaleModuleSheaf G := by
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (IsConstructibleSheaf.of_iso e)

end AlgebraicGeometry.Scheme
