/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.Pretopology

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.ConstantLocalModuleHomSupplement
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleUnitSupplement
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalModuleIsoSupplement
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Interval
import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.FiniteFreeResolution
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import Mathlib.CategoryTheory.Sites.LocallyInjective
import WeilConjectures.ProperBaseChange.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.SingleHomology

/-! # One step of the coefficient-ideal filtration

Source: Stacks Project, Cohomology on Sites, Tag 094I.
-/

@[expose] public section


universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace SheafOfModules


attribute [local irreducible] monoidalCategory in
private noncomputable def coefficientMap
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D) :
    constantCoefficientRing T B ⟶ constantCoefficientRing T D :=
  (sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).map
    ((constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f))

section CoefficientTensor

open MonoidalCategory

variable {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
  {R S A : Sheaf T CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡(" E ")" => (sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).obj E
set_option hygiene false in
local notation "𝓻(" f ")" => (sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).map f

end CoefficientTensor

section TensorSequence

open MonoidalCategory

variable {V : Type*} [Category V] [Abelian V] [MonoidalCategory V]
  [MonoidalPreadditive V]

attribute [local instance] tensorComplex_additive

end TensorSequence

end SheafOfModules
