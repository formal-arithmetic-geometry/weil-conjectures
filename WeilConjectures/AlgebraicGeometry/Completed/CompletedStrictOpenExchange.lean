/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.CategoryTheory.Derived.DerivedPairExchangeNormalization
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import all WeilConjectures.Algebra.Homology.ProperBaseChange.DiagramKFlatReplacements
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenKFlat
import WeilConjectures.AlgebraicGeometry.Adic.AdicPullbackPresentationModels
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Strict open exchange over completed coefficient rings

Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange before Rlim;
Stacks Project, Tags 03DI, 03DJ, 04J0 and 06XN.
(blueprint: def-cbc-completed-strict-open-exchange).

All tower operations precede derived inverse limits. The ordinary inverse exchange
is the already specified adjoint conjugate of the sectionwise cartesian comparison.
Its strict lift and its derived descent retain that normalization. Positive level
n+1 is encoded by n : ℕ. No completeness or quasi-compactness is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint limit SheafOfModules.pushforward
  SheafOfModules.extensionByZeroPresheaf PresheafOfModules.sheafification
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory.Q DerivedCategory.Qh

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Additivity is checked at every tower index.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: extension presheaves, sheafification and slice transport are additive;
apply their sum equation to each component of a tower morphism. -/
@[instance] theorem cbcStrictOpenModule_additive {U X : Scheme.{u}}
    (j : U ⟶ X) (hj : IsOpenImmersion j) : (cbcStrictOpenModule d j hj).Additive := by
  dsimp only [cbcStrictOpenModule]
  infer_instance

/-- Exactness of extension on towers is levelwise, with no condition on the open.
Source: Stacks 03DJ (blueprint: def-cbc-completed-strict-open-exchange).
Proof: kernels and cokernels of strict diagrams are levelwise. Exactness of
sheafified slice extension therefore preserves both finite limits and colimits. -/
@[instance] theorem cbcStrictOpenModule_limits {U X : Scheme.{u}}
    (j : U ⟶ X) (hj : IsOpenImmersion j) :
    PreservesFiniteLimits (cbcStrictOpenModule d j hj) := by
  dsimp only [cbcStrictOpenModule]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Finite colimits are preserved at each tower index.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: the slice extension is left adjoint to restriction, hence preserves finite
colimits. Colimits of strict diagrams are computed at each index. -/
@[instance] theorem cbcStrictOpenModule_colimits {U X : Scheme.{u}}
    (j : U ⟶ X) (hj : IsOpenImmersion j) :
    PreservesFiniteColimits (cbcStrictOpenModule d j hj) := by
  dsimp only [cbcStrictOpenModule]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

/-- The simultaneous strict maps are inverse, component by component.
Source: Stacks 03DI (blueprint: def-cbc-completed-strict-open-exchange).
Proof: the inverse at each index is the forward ordinary exchange. Naturality
makes both maps strict; their composites are identities at each index. -/
@[instance] theorem cbcStrictInverseModule_isIso : IsIso (cbcStrictInverseModule d sq) := by
  have (M : pbcTowers U (pbcAdicCompletion U d)) :
      IsIso ((cbcStrictInverseModule d sq).app M) := by
    have (n : ℕᵒᵖ) : IsIso (((cbcStrictInverseModule d sq).app M).app n) := by
      change IsIso ((cbcUnderivedInverseExchange d sq).app (M.obj n))
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

attribute [local irreducible] cbcStrictOpenModule completedTowerModulePullback
  completedTowerPullbackCounit cbcStrictInverseModule cbcUnderivedInverseExchange

/-- The canonical strict exchange, selected by its unique representative equation.
Source: Stacks 03DI, 06XN (blueprint: def-cbc-completed-strict-open-exchange). -/
@[irreducible] def cbcStrictExchange := (cbcStrictExchange_existsUnique d sq).exists.choose

end AlgebraicGeometry.Scheme
