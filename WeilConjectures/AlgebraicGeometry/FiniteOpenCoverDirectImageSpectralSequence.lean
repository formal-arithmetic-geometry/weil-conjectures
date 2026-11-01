/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import WeilConjectures.AlgebraicGeometry.Sites.KInjectiveComparisonPrinciple
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Order.Fin.Basic

public import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
public import WeilConjectures.Algebra.Homology.TotalComplexRowResolution

/-! # Ordered finite-open-cover spectral sequence for etale direct images

Source: Stacks Project, sites-cohomology.tex, Tag 03AZ, relative ordered variant;
homology.tex, Tags 0130 and 0132
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence).

The spectral sequence and its finite abutment filtration live in the functor category
of module sheaves. The first-page comparison with the actual higher direct images is
normalized by the canonical comparison on restricted injective resolutions. Thus the
first differential is the alternating sum of the canonical restrictions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

/-- The actual higher direct image of the restricted sheaf, as a functor in M.
Source: Stacks 03AZ, relative variant, and derived.tex, Tag 013K
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverHigherImage (f : X ⟶ Y) (U : X.Opens) (q : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) :=
  upperStar (ModuleCat.{u + 1} B) U.ι ⋙
    (lowerStar (ModuleCat.{u + 1} B) (U.ι ≫ f)).rightDerived q

/-- Intersection indexed by a strictly increasing tuple of cover indices.
Source: Stacks 03AZ, relative ordered variant
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverIntersection {m p : ℕ} (U : Fin m → X.Opens)
    (a : Fin (p + 1) ↪o Fin m) : X.Opens :=
  ⨅ k : Fin (p + 1), U (a k)

/-- The first-page direct sum of the actual higher direct images.
The index type is finite, and empty when p is at least m.
Source: Stacks 03AZ, relative ordered variant
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverPageOne (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens) (p q : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) :=
  biproduct (fun a : Fin (p + 1) ↪o Fin m ↦
    finiteCoverHigherImage B f (finiteCoverIntersection U a) q)

set_option maxHeartbeats 1200000 in
-- The normalized first-page differential has several dependent functor-category composites.
end AlgebraicGeometry.Etale
