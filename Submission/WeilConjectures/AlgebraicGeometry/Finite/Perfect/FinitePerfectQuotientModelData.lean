/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicKoszulConstruction
public import Submission.WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
public import Submission.WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Submission.WeilConjectures.AlgebraicGeometry.KoszulDifferential
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Submission.WeilConjectures.CategoryTheory.Constant.ConstantModuleKFlat
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Submission.WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Data for finite perfect quotient models

Source: Stacks Tags 09C2 and 094I
(blueprint: def-weil-pbc-finite-perfect-quotient-model-data).

This interface records finite-level models without asserting a completed realization.
All coefficient identifications are normalized on constant sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

/-- The locally bijective characterization at the actual coefficient universe.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: the small pro-etale site is essentially small in universe t+1. -/
theorem finitePerfectModelsAbLocallyBijective (X : Scheme.{t}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Standard algebraic derived localization.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsAlgebraHasDerived (A : Type t) [CommRing A] :
    HasDerivedCategory (ModuleCat.{t} A) := HasDerivedCategory.standard _
/-- Standard derived localization for the actual coefficient sheaves.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsRingHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    HasDerivedCategory (SheafOfModules.{t + 1} R) := HasDerivedCategory.standard _
/-- Local bijectivity on the concrete localized site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceAbLocallyBijective (X : Scheme.{t}) (U : X.ProEt) :
    ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
/-- Standard derived localization on each slice.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt) :
    HasDerivedCategory (SheafOfModules.{t + 1} (R.over U)) :=
  HasDerivedCategory.standard _

end AlgebraicGeometry.Scheme
