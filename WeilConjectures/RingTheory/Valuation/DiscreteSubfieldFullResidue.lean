/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FieldTheory.PBasis
public import WeilConjectures.RingTheory.Valuation.IntegralClosureHenselianDVR
public import WeilConjectures.RingTheory.Valuation.ResiduallyIndependentRadicals

/-!
# A discrete subfield with the full residue field

Let `R` be a henselian discrete valuation ring with separably closed residue field `κ` of
exponential characteristic `p`, and let `Ω` be an algebraically closed field algebraic over `R`,
with the valuation ring `𝒪 = integralClosureValuationSubring R Ω`. We construct a subfield
`K₀ ⊆ Ω` containing the fraction field `K` of `R` such that

* the values of `K₀` are the values of `K` (powers of the value of a uniformizer `ϖ` of `R`),
* every element of `𝒪` is congruent modulo the maximal ideal to an element of `K₀ ∩ 𝒪`.

Construction: lift a `p`-basis `b` of `κ` to units `t i` of `R`, and adjoin to `K` compatible
`p ^ n`-th roots `θ i n` of the `t i` (`θ i (n + 1) ^ p = θ i n`). The finite level fields
`K(θ i n : i ∈ s)` are unramified of degree `p ^ (n * #s)` over `K`
(`ValuationSubring.finrank_adjoin_eq`), so `K₀` is discrete; its residue field contains all
`p ^ n`-th roots of elements of `κ`, hence is the residue field of `𝒪` (the perfect closure of
`κ`).

## Main statements

- `Field.exists_powIndependent_closure`: a `p`-basis in the form used here.
- `IsDiscreteValuationRing.exists_discrete_subfield_full_residue`: the construction.
-/

@[expose] public section

open IsLocalRing IntermediateField

universe u

namespace Field

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Field

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {Ω : Type*} [Field Ω] [Algebra R Ω] [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω]

@[inherit_doc] local notation "𝒪" => integralClosureValuationSubring R Ω

section RootSystem

/-! ### Compatible systems of `p ^ n`-th roots of units -/

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K Ω]
  [IsScalarTower R K Ω] {ι : Type*} {t : ι → Rˣ} {θ : ι → ℕ → Ω}

end RootSystem

end IsDiscreteValuationRing
