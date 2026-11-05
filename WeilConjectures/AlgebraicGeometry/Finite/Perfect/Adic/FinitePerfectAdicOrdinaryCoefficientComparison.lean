/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicFreeTensorCone
public import WeilConjectures.AlgebraicGeometry.Adic.AdicOrdinaryTensorDiagram
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleOrdinaryRealization
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Ordinary completed realization and the quotient coefficient tensors

Source: Stacks Project, Tag 09C6; Modules on Sites, Tags 093J--093M.
This comparison takes place entirely in the abelian module categories.
(blueprint: lem-weil-pbc-finite-perfect-adic-ordinary-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
-- Only the binary tensor comparison and its naturality are needed below.

namespace AlgebraicGeometry.Scheme

-- Pin the coefficient universe of the site instead of inferring an ambient lift.
attribute [local instance] comparisonSiteSmall

@[instance_reducible] private def constantModulesMonoidal
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    MonoidalCategory (SheafOfModules.{t + 1} (adicModuleRing X A)) :=
  CategoryTheory.ConstantScalarRestriction.ringMonoidal.{t + 1, t}
    (ProEt.topology X) (ULift.{t + 1} A)
attribute [local instance] constantModulesMonoidal

attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local irreducible] completedAdicChangeData completedAdicRing

@[instance_reducible] private def constantMonoidal
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    @Functor.Monoidal (ModuleCat.{t + 1} (ULift.{t + 1} A)) _ _
      (SheafOfModules.{t + 1} (adicModuleRing X A)) _ (constantModulesMonoidal X A)
      (koszulConstantFunctor X A) := by
  letI := constantModulesMonoidal X A
  let J := ProEt.topology X
  let R := ULift.{t + 1} A
  letI : MonoidalCategory (Sheaf J (ModuleCat.{t + 1} R)) :=
    CategoryTheory.ConstantScalarRestriction.fixedMonoidal.{t + 1, t} J R
  letI : (presheafToSheaf J (ModuleCat.{t + 1} R)).Monoidal :=
    (sfbSheafTensorStructure.{t, t + 1, t + 1, t + 1, t + 2}
      (A := ModuleCat.{t + 1} R) J).sheafificationMonoidal
  letI : (constantSheaf J (ModuleCat.{t + 1} R)).Monoidal :=
    inferInstanceAs (Functor.const X.ProEtᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{t + 1} R)).Monoidal
  let e := (CategoryTheory.ConstantScalarRestriction.restriction.{t + 1, t} J R).asEquivalence
  letI : e.functor.Monoidal :=
    (CategoryTheory.ConstantScalarRestriction.restrictionBraided.{t + 1, t} J R).toMonoidal
  letI := e.inverseMonoidal
  exact e.monoidalOfPostcompFunctor (koszulConstantFunctor X A) (constantFixedIso X A).symm

end AlgebraicGeometry.Scheme
