/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-! # Canonical rational triangulation adapters

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-triangulation-adapters)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace CategoryTheory.ScalarLocalization
open scoped TensorProduct

end CategoryTheory.ScalarLocalization

namespace AlgebraicGeometry.Scheme
section Triangulation
variable (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- Expose the existing rational-transport triangulation through Fact hypotheses.
This is the same selected witness as pbcRationalTriangulationData;
its shift and image-triangle normalizations are retained. These data adapters allow
instance synthesis when the raw category abbreviation erases the geometric proofs.
Source: blueprint order 1305 (blueprint: lem-pbc-scalar-triangulation-adapters).
Proof: Project existence of a zero object from pbcRationalTriangulationData. The raw
category is unchanged, so this is exactly the required HasZeroObject proposition. -/
@[instance] theorem pbcScalarRationalZero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    HasZeroObject (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) := by
  exact (pbcRationalTriangulationData l E T Fact.out Fact.out).choose

/-- Expose the existing rational-transport triangulation through Fact hypotheses.
This is the same selected witness as pbcRationalTriangulationData;
its shift and image-triangle normalizations are retained. These data adapters allow
instance synthesis when the raw category abbreviation erases the geometric proofs.
Source: blueprint order 1305 (blueprint: lem-pbc-scalar-triangulation-adapters).
Proof: Project additive shifts from pbcRationalTriangulationData. The preceding
HasShift adapter is its identical chosen shift, and all other class arguments
are propositions, so proof irrelevance identifies their proofs. -/
@[instance] theorem pbcScalarRationalShiftAdditive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    ∀ n : ℤ, (shiftFunctor (PbcRationalCategory T (pbcIntegralDatum l E)
      (pbcUniformizer l E)) n).Additive := by
  exact (pbcRationalTriangulationData l E T Fact.out Fact.out).choose_spec.choose_spec.2.choose

end Triangulation
end AlgebraicGeometry.Scheme
