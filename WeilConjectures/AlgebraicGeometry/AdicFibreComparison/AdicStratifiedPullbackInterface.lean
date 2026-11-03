/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.NormalizedFibre.AdicNormalizedFibreData
public import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.TensorProduct.Finite
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarStandardCohomology
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.Localized.LocalizedTStructure
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeGeometryFibreBound
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeConstructibleScalarTransport
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
public import WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus
public import WeilConjectures.CategoryTheory.StageSystem.PbcVerdierAxioms
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
public import WeilConjectures.ProperBaseChange.CondensedERealizationSystem
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedEIntegralExchange
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERationalCondensedExchange
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
public import WeilConjectures.SixFunctors.Supporting.IntrinsicQbarCategory
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # The standard-heart interface of actual completed pullback

Source: Bhatt--Scholze, Remark 6.8.15 and Proposition 6.8.14
(blueprint: lem-per-adic-stratified-pullback-texact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [hl : Fact (IsUnit (l : k))]

/-- Reuse the existing separated finite-type base without introducing another bundle.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
abbrev FiniteTypeBase := WeilConjectures.CondensedERealization.Base

/-- The geometric consequences of the stated finite-type hypotheses.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact).
Proof: finite type over Spec k gives noetherianity. The finite-type fibre-dimension theorem
on its unique fibre bounds dimension. -/
theorem finiteTypeBaseGeometry (X : FiniteTypeBase k) :
    IsNoetherian X.scheme ∧ (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) := by
  sorry

include hl in
/-- Invertibility of the coefficient prime follows from the stated base-field hypothesis.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact).
Proof: the structure morphism sends the unit l in k to a unit in every local ring. -/
theorem finiteTypeBasePrime (X : FiniteTypeBase k) :
    ∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x) := by
  sorry

/-- The dimension hypothesis is a consequence of finite type over the base field.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
instance finiteTypeBaseDimension (X : FiniteTypeBase k) :
    Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) :=
  ⟨(finiteTypeBaseGeometry X).2⟩

/-- The coefficient prime stays invertible in each local ring.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
instance finiteTypeBasePrimeUnit (X : FiniteTypeBase k) :
    Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x)) :=
  ⟨finiteTypeBasePrime l X⟩

/-- The existing finite-type base, viewed in the continuous realization interface.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def base (X : FiniteTypeBase k) : ContinuousRational.Base.{u} l where
  scheme := X.scheme
  dimension := (finiteTypeBaseDimension X).out
  prime_unit := (finiteTypeBasePrimeUnit l X).out

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (R : ContinuousRational.Family.{u} l)

end AlgebraicGeometry.Scheme.AdicFibreComparison
