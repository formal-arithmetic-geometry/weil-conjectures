/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V7
-/
module

public import Sheaf.Paper.FdPullbackAugmentationCounitMatching
public import Sheaf.Paper.PullbackCommonStrictTowerModels

/-! # Uniqueness of the normalized integral pullback comparison

Source: trace-definition whole-tower comparison, steps 8--10; Stacks 0941 and 099N.
(blueprint: lem-fd-pullback-roos-matching-uniqueness). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- A finite comparison matched to the normalized Roos realization is inverse to
any common strict-tower comparison.
Source: trace-definition whole-tower comparison, steps 8--10; Stacks 0941 and 099N
(blueprint: lem-fd-pullback-roos-matching-uniqueness).

Proof: choose a flat-term K-flat representative of the integral constructible input.
Use the strict tower isomorphism of the common model to present its framework
quotient tower. The matching equations and the common model's cone normalization
express both comparisons using the same actual completion unit and the same
quotient augmentation. The two cone coordinates are fixed by the quotient
projections and the zero shifted augmentation coordinate. On a K-injective tower
resolution the normalized Roos comparison is H(q) followed by inverse iota;
its resolution formula identifies the two entire-tower realizations. Cancel the
invertible realization maps and the framework augmentation on the complete input.
This identifies the matching b with the common model comparison. Invert and use
the first matching clause to identify the selected ambient component. Naturality
transports this equality along the representative isomorphism to the input K.
This uses no inverse of a quotient transition and applies to zero inputs and
identity scheme maps as well. -/
theorem fdPullbackRoosMatching_uniqueness
    {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
    (h : U ≅ T) (E : Padic.FiniteCoefficientFields l Ω)
    (R : IntegralComparisonSystem.{u} l) (d : FdPullbackComparison l Ω CU CT h E)
    (hm : FdPullbackRoosMatching l Ω CU CT h E R d)
    (b : FdCommonStrictTowerModels l (pbcFiniteField.{u} l Ω E) h)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    d.ambient.hom.app K = b.actual_ambient.inv.app K := by sorry

end WeilConjectures
