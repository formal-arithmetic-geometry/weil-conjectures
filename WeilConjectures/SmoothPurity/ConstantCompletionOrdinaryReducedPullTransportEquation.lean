/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.ProperBaseChange.FlatAlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.ProperBaseChange.RingedToposPullbackFilteredColimits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.ProperBaseChange.ConstantCompletionOrdinaryPullComparison
public import WeilConjectures.ProperBaseChange.ConstantCompletionCore
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
import all WeilConjectures.SmoothPurity.ConstantCompletionOrdinaryFinitePullExistence
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.RingTheory.Ideal.Defs
import all WeilConjectures.ProperBaseChange.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement

/-! # Normalized ordinary reduced transport equation

This records the normalized comparison equation after both transports have been
constructed.
(blueprint: lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.ConstantCompletion

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]

attribute [local irreducible] completed derivedExtension

omit hL in
private theorem pullInsertion_naturality {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} (c : F.rings.obj R ⟶ S)
    {M N : Mod R} (f : M ⟶ N) :
    pullInsertion F c M ≫ (underlying S).map ((pull F c).map f) =
      L.map ((underlying R).map f) ≫ pullInsertion F c N := by
  dsimp only [pullInsertion, pull, Functor.comp_map]
  erw [Category.assoc, finiteInsertion_naturality J' c,
    ← Category.assoc, ← (F.algebra R).moduleUnderlying.inv.naturality f, Category.assoc]

include V adj hL in
omit hL in
attribute [local semireducible] completed

omit hL in
attribute [local irreducible] completed

set_option maxHeartbeats 400000 in
-- Two adjunction units and four whiskered isomorphisms require extra elaboration heartbeats.
omit hL in
end CategoryTheory.ConstantCompletion
