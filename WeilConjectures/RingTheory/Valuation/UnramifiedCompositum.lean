/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ResiduallyIndependentRadicals

/-!
# Adjoining `p ^ n`-th roots of `p`-independent units

Let `𝒪` be a valuation subring of a field `Ω` whose residue field has exponential
characteristic `p`, and let `F ⊆ Ω` be the fraction field of a local ring `R` with
`𝒪 ∩ F = R` (e.g. `F` discretely valued with valuation ring `R`). If `t i` (`i ∈ ι`, finite)
are units of `R` whose residues are `p`-independent in the residue field of `R`, and
`θ i ^ p ^ n = t i`, then `F(θ)` is unramified over `F`:

* every value of `F(θ)` is a value of `F` (so if `F` has value group `v(ϖ) ^ ℤ`, so has `F(θ)`);
* `[F(θ) : F] = p ^ (n * #ι)`, with basis the monomials `∏ i, θ i ^ E i`, `0 ≤ E i < p ^ n`;
* every `y ∈ F(θ)` is `∑ c E • ∏ i, θ i ^ E i` with `v (c E) ≤ v y`; in particular the residue
  field of `F(θ)` is generated over the residue field of `F` by the residues of the `θ i`.

This applies to the compositum `K_j · F'` of a level field
`K_j = K(θ i n : i ∈ s)` of `IsDiscreteValuationRing.exists_discrete_subfield_full_residue`
with a discretely valued field `F'` (with valuation ring `R'`) in whose residue field the
residues of the `t i` stay `p`-independent: `K_j · F' = F'(θ i n : i ∈ s)`.
-/

@[expose] public section

open IsLocalRing IntermediateField Module

namespace ValuationSubring

variable {Ω : Type*} [Field Ω] (𝒪 : ValuationSubring Ω) {R F : Type*} [CommRing R]
  [IsLocalRing R] [Field F] [Algebra R F] [IsFractionRing R F] [Algebra F Ω] [Algebra R Ω]
  [IsScalarTower R F Ω] {p : ℕ} [ExpChar (ResidueField 𝒪) p] [ExpChar (ResidueField R) p]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ι → R} {θ : ι → Ω} {n : ℕ}

end ValuationSubring
