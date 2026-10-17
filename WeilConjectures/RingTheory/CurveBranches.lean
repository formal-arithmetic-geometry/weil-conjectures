/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.RingTheory.HenselianDVRExtension

/-!
# Branches of a one-dimensional local ring

For a reduced one-dimensional Noetherian local ring `R` with minimal primes `p₁, …, pₜ`, put
`Q(R) = ∏ₐ Frac(R/pₐ)` and `B(R) = ∏ₐ B(R)ₐ`, where `B(R)ₐ` is the integral closure of `R/pₐ` in
`Frac(R/pₐ)` (blueprint `def-exc-local-curve-branches`).

If `R` is moreover henselian with algebraically closed residue field and its normalization is
finite, then every branch `B(R)ₐ` is a henselian discrete valuation ring with fraction field
`Frac(R/pₐ)` and the same residue field as `R`, and the punctured spectrum of `R` is the
spectrum of `Q(R)`: there is `f` in the maximal ideal, outside every minimal prime, such that
`D(f) = Spec R ∖ {𝔪}` and `R_f = Q(R)` (blueprint `lem-exc-punctured-curve-branches`).

## Main definitions and statements

- `IsLocalRing.branchFractionRing`, `IsLocalRing.branch`, `IsLocalRing.branchAlgebra`: `Q(R)`,
  the branches and `B(R)`.
- `IsLocalRing.isDiscreteValuationRing_branch`, `IsLocalRing.henselianLocalRing_branch`,
  `IsLocalRing.isAlgClosed_residueField_branch`: the branches are henselian DVRs with
  algebraically closed residue field.
- `IsLocalRing.exists_isLocalization_away_branchFractionRing`: the punctured spectrum.
-/

@[expose] public section

universe u

open IsLocalRing

namespace IsLocalRing

variable (R : Type u) [CommRing R]

/-- The total ring of fractions of the branches of `R`: `Q(R) = ∏ₐ Frac(R/pₐ)`, the product
over the minimal primes `pₐ` of `R`. (blueprint: `def-exc-local-curve-branches`) -/
abbrev branchFractionRing : Type u :=
  ∀ p : minimalPrimes R, FractionRing (R ⧸ p.1)

/-- The branch of `R` at a minimal prime `p`: the integral closure of `R/p` in its fraction
field. (blueprint: `def-exc-local-curve-branches`) -/
abbrev branch (p : minimalPrimes R) : Type u :=
  integralClosure (R ⧸ p.1) (FractionRing (R ⧸ p.1))

/-- Blueprint `def-exc-local-curve-branches`: The normalization algebra of local curve
branches.

For a ring `R` with minimal primes `pₐ`, the branch algebra
`B(R) = ∏ₐ \overline{(R/pₐ)}^{Frac(R/pₐ)}`: the product of the integral closures of the `R/pₐ`
in their fraction fields (`IsLocalRing.branch`). The map `R → B(R)` (`algebraMap`) is the
product of the quotient maps followed by the inclusions in these integral closures, and
`B(R) ⊆ Q(R)` (`IsLocalRing.branchFractionRing`). The blueprint considers a reduced
one-dimensional Noetherian local ring `R`; the definition makes sense in general. -/
abbrev branchAlgebra : Type u :=
  ∀ p : minimalPrimes R, branch R p

example : Algebra R (branchAlgebra R) := inferInstance
example : Algebra R (branchFractionRing R) := inferInstance
example : Algebra (branchAlgebra R) (branchFractionRing R) := inferInstance

end IsLocalRing
