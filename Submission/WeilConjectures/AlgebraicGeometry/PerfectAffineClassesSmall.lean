/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Small.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Submission.WeilConjectures.RingTheory.RingPseudoCoherent
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Submission.WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.CategoryTheory.Localization.Equivalence
import Submission.WeilConjectures.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.Single
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullback
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.Algebra.Homology.KFlatPullback
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullback
import Submission.WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Submission.WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Data.Finset.Max
import Submission.WeilConjectures.RingTheory.MPseudoCoherent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Localization.Away.Basic
import Submission.WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import Submission.WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import Submission.WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Flat.Localization
import Submission.WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Submission.WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Free
import Submission.WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Submission.WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Submission.WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import Mathlib.CategoryTheory.Whiskering
import Submission.WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.RingTheory.Localization.BaseChange
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import Submission.WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Submission.WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Data.Int.Interval
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.RingTheory.Finiteness.Projective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.CategoryTheory.Adjunction.Unique
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Smallness of perfect isomorphism classes on an affine scheme

Source: Step 1 of lem-pc-perfect-complexes-compact-set, using Stacks Project,
Tag 08EB (blueprint: lem-pc-perfect-affine-classes-small).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Small encoding of a complex with finitely generated terms. -/
private structure FiniteTermModel (A : Type u) [CommRing A] : Type u where
  X : ℤ → FGModuleRepr A
  d : ∀ i j : ℤ, ModuleCat.of A (X i) ⟶ ModuleCat.of A (X j)
  shape : ∀ i j : ℤ, ¬(ComplexShape.up ℤ).Rel i j → d i j = 0
  square : ∀ i j k : ℤ, d i j ≫ d j k = 0

end AlgebraicGeometry.Scheme
