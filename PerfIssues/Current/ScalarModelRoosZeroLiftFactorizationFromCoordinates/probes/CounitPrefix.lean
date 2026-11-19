/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import all WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftUniqueness
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosCounitNormalization

/-! # Factorization from normalized scalar Roos coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedScalarChangeData

attribute [local implicit_reducible] completedOrdinaryScalarComplex integralOperationsRoos
  completedDerivedScalarExtension completedScalarCounit completedOrdinaryScalarExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

/-- Naturality of the universal cochain counit, without expanding scalar-change data.
Source: Stacks 06YY; the homotopy counit's naturality square. -/
private theorem scalarCounit_natural
    {A B : CochainComplex (integralTowerModules l L X) ℤ} (g : A ⟶ B) :
    (completedDerivedScalarExtension l L F j X).map (DerivedCategory.Q.map g) ≫
        completedScalarCounit l L F j X B =
      completedScalarCounit l L F j X A ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l L F j X).map g) := by
  dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]
  with_unfolding_all
    exact homotopyCounit_naturality
      (completedOrdinaryScalarExtension.{u, u} l L F j X)
      (completedDerivedScalarExtension.{u, u} l L F j X)
      ((completedScalarChangeData.{u, u} l L F j X).choose_spec.choose_spec.choose_spec
        |>.choose_spec.2.2.choose_spec.choose) g

end WeilConjectures
