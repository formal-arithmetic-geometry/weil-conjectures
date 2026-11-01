/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedCoefficientReduction
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
import WeilConjectures.AlgebraicGeometry.Cartier.CartierSourceComparisonGenerator

/-!
# Supported source comparison satisfies the Cartier quotient unit square

Source: blueprint `lem-route-cartier-source-unit-square`, final paragraph of
`lem-amb-cartier-kummer-map.proof.md` (blueprint: lem-route-cartier-source-unit-square).

The statement is the finite-Tate specialization of the general supported-generator
identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/--
For a prime `ℓ`, a finite extension `E / Q_ℓ`, and `n : ℕ`, the canonical
supported source comparison obeys the quotient-unit square.  Here `n : ℕ`
expresses the stated `n ≥ 0` clause, `i` is a closed immersion, and all maps
are the canonical maps named in the node statement.

Source: blueprint `lem-route-cartier-source-unit-square`, final paragraph of
`lem-amb-cartier-kummer-map.proof.md` (blueprint: lem-route-cartier-source-unit-square).
Proof (one step): apply the first displayed equality of the general
supported-generator identity (blueprint: lem-sfb-cartier-source-comparison-generator,
now declared as `cartierSourceComparison_supportedConstantUnit`) with the
commutative coefficient ring
`A = finiteTateCoefficient ℓ E n`, the scheme `Z = T` and the closed immersion `i`;
its `e_i`, `γ_Z`, `ρ^i_A` and `u_i` are `geoCartierSourceComparison A i`,
`cartierConstantComparison A T`, `proEtaleConstantDirectImageMap i` (the map
underlying `cartierSupportedUnit` after unfolding `cartierSupported`) and
`supportedConstantUnit A i`.  Its consequence about automorphisms is unused.
The empty support and identity-immersion cases are included by the same canonical maps.
-/
theorem cartierSourceUnitSquare (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    (comparisonUpperStar
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).map
          (Etale.supportedConstantUnit
            (Scheme.finiteTateCoefficient l E n) i) ≫
        geoCartierSourceComparison
          (Scheme.finiteTateCoefficient l E n) i =
      Etale.cartierConstantComparison
          (Scheme.finiteTateCoefficient l E n) T ≫
        Scheme.proEtaleConstantDirectImageMap i
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
          (ModuleCat.of (Scheme.finiteTateCoefficient l E n)
            (Scheme.finiteTateCoefficient l E n)) := by
  exact cartierSourceComparison_supportedConstantUnit
    (Scheme.finiteTateCoefficient l E n) i

end AlgebraicGeometry.ProEtale
