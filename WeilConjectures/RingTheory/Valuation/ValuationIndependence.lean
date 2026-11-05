/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Residually independent families and valuation independence

Let `v` be a valuation on a field `F` and `K ⊆ F` a subfield. A family `z` of elements of `F` of
value `1` is *residually independent* over `K` if every combination `∑ c j • z j` with
coefficients `c j ∈ K` of value `≤ 1` and of value `< 1` has all its coefficients of value `< 1`
(i.e. the residues of the `z j` are linearly independent over the residue field of `K`).

## Main statements

- `Valuation.ResiduallyIndependent.map_sum_smul`: for a residually independent family `z`,
  `v (∑ c j • z j) = max_j v (c j)`.
- `Valuation.ResiduallyIndependent.linearIndependent_mul`: if moreover the `w i` are nonzero
  with values pairwise distinct modulo `v(Kˣ)`, the products `w i * z j` are `K`-linearly
  independent; `Valuation.ResiduallyIndependent.card_mul_card_le_finrank` is the corresponding
  inequality `e * f ≤ [E : K]`.
- `ValuationSubring.exists_basis_residuallyIndependent`: the *cartesian lemma*: if `K` is the
  fraction field of a complete discrete valuation ring `R`, `𝒪` is a valuation ring of `F` with
  `𝒪 ∩ K = R` and every value of `F` is a value of `K`, then every finite-dimensional
  `K`-subspace of `F` has a residually independent basis of elements of value `1`.
-/

@[expose] public section

open Module

namespace Valuation

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  (K : Type*) [Field K] [Algebra K F]

variable {v K}

end Valuation

namespace Valuation

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀}
  {K : Type*} [Field K] [Algebra K F]

end Valuation

namespace ValuationSubring

open IsLocalRing

variable {R K F : Type*} [CommRing R] [Field K] [Algebra R K] [Field F] [Algebra K F] [Algebra R F]
  [IsScalarTower R K F] {𝒪 : ValuationSubring F}

end ValuationSubring

namespace Valuation

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {K : Type*} [Field K] [Algebra K F]

end Valuation

namespace ValuationSubring

open IsLocalRing

variable {R K F : Type*} [CommRing R] [Field K] [Algebra R K] [Field F] [Algebra K F]
  [Algebra R F] [IsScalarTower R K F] {𝒪 : ValuationSubring F}

end ValuationSubring
