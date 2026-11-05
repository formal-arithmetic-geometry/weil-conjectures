/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.AdicDualityTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange

/-!
# Duality for the cohomology of `ℚ̄_ℓ` from duality with coefficients `ℤ/ℓᵐ`

Let `S` be a quasi-compact quasi-separated scheme whose pro-étale cohomology groups
`Hᵏ(S, ℤ/ℓᵐ)` are finite. This file transports dualities between the finite-level cohomology
groups `Hⁱ(S, ℤ/ℓᵐ)` and `Hʲ(S, ℤ/ℓᵐ)` — nondegenerate pairings with values in `ℤ/ℓᵐ` which are
similitudes for given endomorphisms (Frobenius) of the integral cohomology — to a perfect
pairing between the cohomology groups `Hⁱ(S, ℚ̄_ℓ)` and `Hʲ(S, ℚ̄_ℓ)` of the constant `ℓ`-adic
sheaf, which is a similitude for the induced endomorphisms
(`AlgebraicGeometry.ProEtale.exists_isPerfPair_adicConstantH`). The finite-level dualities need
not be compatible with each other.

The ingredients are: finite generation of `Hⁿ(S, ℤ_ℓ)` and the Bockstein sequences
(`WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology`),
`Hⁿ(S, ℚ̄_ℓ) = ℚ̄_ℓ ⊗ Hⁿ(S, ℤ_ℓ)`
(`AlgebraicGeometry.ProEtale.isBaseChange_integralToAdicConstantH`)
and the linear algebra of `LinearMap.exists_isPerfPair_of_finiteLevel`. This is the transport
step of blueprint `thm-pod-derived-poincare-duality` (`sk-thm-transport`), for the constant
coefficient sheaf.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u})

end AlgebraicGeometry.ProEtale
