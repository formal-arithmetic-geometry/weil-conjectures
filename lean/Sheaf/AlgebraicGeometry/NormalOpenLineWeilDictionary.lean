/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Sheaf.RingTheory.HeightOneFractionOrder
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.InvertibleModuleGenericStalk
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Weil divisor data of an invertible sheaf on an open normal affine scheme

Source: Stacks Project, Divisors, Tags 02SF, 02SG, 0BE6 and 0BE8
(blueprint: lem-sfb-normal-open-line-weil-dictionary).

The normalized valuation is the existing `Ring.weilFractionOrder`. The finite
family is indexed by precisely the height-one primes belonging to the open.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible sheaf on a nonempty open of a normal Noetherian affine domain
has finite Weil divisor data, locally principal at every point, and it is trivial
exactly when the same data are globally principal.
Source: Stacks Project, Divisors, Tags 02SF (local coefficients), 02SG (support),
0BE6 (the associated divisor) and 0BE8 (injectivity of the divisor-class map)
(blueprint: lem-sfb-normal-open-line-weil-dictionary).

Proof:
1. By `lem-weil-pbc-spec-domain-stalks-function-field`, the spectrum is integral,
its stalks are the prime localizations and its function field is `FractionRing A`.
The nonempty open remains integral with that function field. Apply
`lem-sc-invertible-module-generic-stalk` to obtain its one-dimensional generic
stalk, injectivity from every stalk, and the criterion for regular sections.
2. Choose a nonempty trivializing open and a frame using `def-sc-invertible-module`.
By `lem-weil-pbc-spec-localization-away-basic-open`, it contains a nonempty basic
open `D(f)`. Let `s` be the generic germ of this frame. At each height-one prime
write `s = b_q e_q` in a local generator, using the generic-stalk lemma.
3. Set `d_q = v_q(b_q)`. Changing the generator multiplies its coefficient by a
local unit, whose valuation is zero by
`lem-trf-normal-domain-principal-divisor-kernel`. Thus the integers are independent
of generators. They vanish on `D(f)` where the chosen section is a frame.
4. Every prime in the support contains `f` and, being height one with `f ≠ 0`,
is minimal over `(f)`. The support is finite by
`lem-sc-finite-minimal-primes-over-ideal`, including the empty support if `D(f)`
is the whole spectrum.
5. At each point `t` choose a frame near `t` and write `s = a_t e` in the generic
stalk. Every height-one prime contained in `t` belongs to that neighborhood,
since opens are stable under generalization. Generator independence gives all
local equations for this one `a_t`. In particular these primes belong to `U`.
6. If `d_q = v_q(a)` globally, divide `s` by `a`. Its coefficient near `t` is
`a_t / a`. By `lem-weil-pbc-localization-noetherian` and
`lem-weil-pbc-localization-normal-domain`, the ring `A_t` is again Noetherian
and normal with the same fraction field. By `lem-weil-pbc-primes-of-localization`
and `lem-weil-pbc-localize-localization-at-prime`, its height-one localizations
are precisely the original `A_q` for `q` contained in `t`. The coefficient has
valuation zero in each, hence is a unit by
`lem-trf-normal-domain-principal-divisor-kernel` applied to `A_t`.
7. The regular-section criterion of `lem-sc-invertible-module-generic-stalk`
glues the divided rational section to a global section. Its germs generate
every stalk, so the map from the structure sheaf sending one to this section
is an isomorphism: in a local frame its coefficient has unit germs and thus
local inverses, which agree on overlaps. Conversely a global frame of a trivial
`L` expresses `s` as `a` times that frame for a single nonzero fraction `a`.
Generator independence gives the global equations for the very same `d`. -/
theorem normal_open_line_weil_dictionary
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (U : (Spec (CommRingCat.of A)).Opens) (hU : Nonempty U)
    (L : U.toScheme.Modules) [L.IsInvertible] :
    ∃ d : {q : Ring.WeilHeightOnePrime A // q.val ∈ U} →₀ ℤ,
      (∀ t : PrimeSpectrum A, t ∈ U → ∃ a : (FractionRing A)ˣ,
        ∀ q : {q : Ring.WeilHeightOnePrime A // q.val ∈ U},
          q.val.val.asIdeal ≤ t.asIdeal → d q = Ring.weilFractionOrder q.val a.val) ∧
      (Nonempty (L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) ↔
        ∃ a : (FractionRing A)ˣ,
          ∀ q : {q : Ring.WeilHeightOnePrime A // q.val ∈ U},
            d q = Ring.weilFractionOrder q.val a.val) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
