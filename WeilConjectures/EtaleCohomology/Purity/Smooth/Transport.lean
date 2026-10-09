/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.ProEtale.Derived.ConstructibleUpperShriek

/-!
# Smooth purity over `𝒪_E`, `E` and `ℚ̄_ℓ`

Smooth purity is proved at the finite coefficient stage in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Basic`. This file is the place for the three
remaining coefficient stages of the `ℓ`-adic formalism (`sk-thm-purity-transport`): the adic
stage over `𝒪_E`, its rationalization over `E`, and the colimit over finite `E/ℚ_ℓ` giving
`ℚ̄_ℓ`. It contains no statement yet.

## Implementation notes

The non-torsion stages live on the *pro-étale* site only: the blueprint makes no assertion for
`𝒪_E`, `E` or `ℚ̄_ℓ` on the small étale site, where the six operations do not have the right
behaviour for discrete non-torsion coefficients (`sk-prop-sf-cbc` (b)). A statement here must
therefore be phrased on `D(X_proét, 𝒪_E)`, where the derived-complete objects are cut out by
`AlgebraicGeometry.DerivedCategory.derivedCompleteIntegral` for the site `Scheme.ProEt.topology X`
and their rationalization is `AlgebraicGeometry.DerivedCategoryDerivedCompleteRational`.

What is missing is the exceptional inverse image at the adic stage. The blueprint defines it
levelwise on normalized systems, `Rf^!(K_n)_n = (Rf^!_n K_n)_n`, from the finite-level functor
`Rf^!_n = ν^* ∘ f^× ∘ Rν_*` of `AlgebraicGeometry.ProEtale.constructibleUpperShriek`, together
with the finite-reduction isomorphisms `Rf^!_n(K_n) ⊗^L A_{E,m} ≅ Rf^!_m(K_m)`. Neither the
reduction functors `D(−, 𝒪_E) ⥤ D(−, A_{E,n})` nor derived limits of such towers are available
here, and the pro-étale `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek` is no substitute:
it assumes that `Rf_!` is a left adjoint on all of `D(Y_proét)`, which fails in general
(`rem:sf-ambient-counterexample`).
-/

-- TODO(unify): sk-thm-purity-transport — define the adic `Rf^!` from
-- `AlgebraicGeometry.ProEtale.constructibleUpperShriek` and the reduction functors, and state
-- `γ_{f,K} : Lf^* K(d)[2d] ≅ Rf^! K` for `K ∈ D^b_{ctf}(Y_proét, Λ)`, `Λ ∈ {𝒪_E, E, ℚ̄_ℓ}`.
