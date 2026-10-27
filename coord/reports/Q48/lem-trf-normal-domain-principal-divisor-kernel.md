## Worker report

The module `Sheaf.RingTheory.NormalDomainPrincipalDivisorKernel` states
`Ring.normalDomain_principalDivisor_kernel`, with one postponed proof matching the
assigned node. Its auxiliary definition `Ring.weilHeightOneLocalizationMap` specializes
Mathlib's actual localization map to the inclusion of the prime-complement denominator
monoid into the nonzero divisors. It has real data and no postponed proof.

The existing, landed definition node `def-trf-height-one-fraction-order` is added to
`stmt_deps`; its `Ring.weilFractionOrder` is used throughout. No new definition node,
dependency repair, or statement correction is needed. The natural-language statement
and proof are unchanged.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Commutative ring R | `R : Type u`, `[CommRing R]` |
| Nontrivial domain | `[IsDomain R]` includes nontriviality and no zero divisors |
| Noetherian | `[IsNoetherianRing R]` |
| Normal domain | `[IsIntegrallyClosed R]`, in conjunction with `[IsDomain R]` |
| K = Frac(R), with R embedded | The canonical `FractionRing R`, with `algebraMap R (FractionRing R)`; its injectivity follows from the domain instance |
| Nonzero primes with no intermediate prime | Existing `Ring.WeilHeightOnePrime R`, whose underlying prime is `q.1.asIdeal` |
| Every height-one localization is a DVR | First conjunct: `∀ q, IsDiscreteValuationRing (Localization.AtPrime q.1.asIdeal)` |
| Normalized additive order | Existing `weilFractionOrder`, with the second conjunct giving `v(j(a) * j(π)^e) = e` for every local unit a, irreducible π and integer e |
| Uniformizer generates the maximal ideal | `Irreducible π`, equivalent to the stated ideal-generator condition by `IsDiscreteValuationRing.irreducible_iff_uniformizer` once the first conjunct supplies the DVR instance |
| Local membership iff v >= 0 | First equivalence of the third conjunct, expressed as existence of a local preimage under the canonical inclusion |
| Local unit membership iff v = 0 | Second equivalence, with a preimage in the local unit group |
| Valuation inequality | Fourth conjunct, `min (v x) (v y) ≤ v (x+y)` for nonzero x, y, and x+y; no valuation property is imposed at zero |
| Finite support on every K-unit | Fifth conjunct, `{q | weilFractionOrder q x ≠ 0}.Finite` |
| Agreement with length-difference orders | Sixth conjunct, for every nonzero a and b, `v(a/b) = weilOrder q a - weilOrder q b`; existing `weilOrder` is the integer-valued length construction of the recorded divisor definition |
| The coordinate formula defines a homomorphism | Seventh conjunct, existence of `div : Additive (FractionRing R)ˣ →+ AffineWeilDivisor R` with every coordinate equal to the existing fraction order; these coordinates uniquely determine div |
| div(xy) = div(x) + div(y), and valuation additivity | `div.map_add`, using `Additive.ofMul`; evaluation at q and the coordinate equation also give the local multiplicative formula |
| Kernel precisely the image of R-units | `div (Additive.ofMul x) = 0 ↔ ∃ a : Rˣ, Units.map (algebraMap R (FractionRing R)).toMonoidHom a = x` |
| Field case: empty H and zero divisor group | Last conjunct, `IsField R → IsEmpty (WeilHeightOnePrime R) ∧ Subsingleton (AffineWeilDivisor R)`; the kernel equivalence still applies in that case |

The existential homomorphism is specified by every coordinate, so it is uniquely
determined by the canonical orders; no arbitrary map is assumed and no data is chosen
from a postponed existence theorem. A separate construction definition is unnecessary
for this theorem statement. There is no assumption that R is Dedekind or has dimension
one, and the universe u is explicitly declared with `R : Type u`.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and
  `isNoetherianRing_iff_ideal_fg`, for the recorded Noetherian definition.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  defined using the canonical fraction ring, for the recorded normal-domain definition.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, the actual
  prime-complement localization, for local rings. The full residue-field/fibre clauses
  of that dependency are not needed in this statement.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `Sheaf.RingTheory.WeilDivisorClassGroup`: `Ring.WeilHeightOnePrime`,
  `Ring.AffineWeilDivisor`, `Ring.weilOrder`. Its class-group quotient is not needed.
- `Sheaf.RingTheory.HeightOneFractionOrder`: `Ring.weilFractionOrder`; its full
  definition subtracts existing orders of the actual `IsLocalization.sec` presentation.
- `Mathlib.RingTheory.Localization.Defs`: `IsLocalization.map`, specializing the
  existing canonical map rather than introducing an arbitrary inclusion.

Plain proof imports retain the stated DAG proof plan: `IsLocalization.isNoetherianRing`
(Localization.Submodule), `isIntegrallyClosed_of_isLocalization`
(IntegralClosure.IntegrallyClosed, already publicly available),
`IsFractionRing.isFractionRing_of_isLocalization` (Localization.LocalizationLocalization),
`IsLocalization.AtPrime.ringKrullDim_eq_height` (Ideal.Height),
`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` (DiscreteValuationRing.Basic,
publicly imported for the statement), `Module.length` and `Module.length_eq_add_of_exact`
(Length), `Ideal.finite_minimalPrimes_of_isNoetherianRing` (Ideal.MinimalPrime.Noetherian),
`AlgebraicGeometry.IsRegular.of_isIntegrallyClosed_stalk` (WeilConjectures.AlgebraicGeometry.Regular;
the recorded DVR proof dependency, also exporting `IsRegularLocalRing.of_isIntegrallyClosed`),
`Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span`
(WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight), and
`Module.injective_pi_localization_associatedPrimes`
(WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes).

Source passages opened: Stacks algebra.tex, 00PD (the equivalences and extension
v(a/b)=v(a)-v(b)), 031T (intersection and associated-prime proof), 02MD (length
order); divisors.tex, 0BE3 (principal divisor) and 02RP (additivity). The eight-step
natural-language proof is included in the theorem docstring, including the local length
calculation, finite support, intersection, unit kernel, and field case.

Edge cases checked before drafting: a field has no nonzero height-one primes, giving
an empty index type and the zero group without any positive-dimensional assumption;
a DVR has one height-one prime and sends a uniformizer power to its integer exponent,
including negative exponents; units and x=1 have zero coordinates; for k[s,t], s/t
has the two expected nonzero coordinates, so no dimension-one restriction is permissible.
The element zero is excluded by the unit domain (and explicitly in the sum inequality).
The zero ring is excluded exactly by the node's domain convention. Rings with nontrivial
class group are allowed: no factoriality or principalness of global primes is assumed.

Searches for an existing statement (via the prescribed msearch.py wrapper):

- leanfinder: “In a Noetherian normal domain the principal Weil divisor map has finite
  support and kernel exactly the units”. Eight results, principally Dedekind-domain
  support lemmas and fractional ideals; none is the arbitrary-dimensional statement.
- loogle: `Ring.ordFrac, IsDiscreteValuationRing, IsIntegrallyClosed`. Zero results.
- grep: `principalDivisor|WeilDivisor|mker_ordFrac`, in Mathlib RingTheory. One result,
  `mker_ordFrac_eq_isUnitSubmonoid`, for a single DVR, not the family of height-one primes.
- leansearch: “The principal Weil divisor of a fraction in a Noetherian normal domain
  is zero if and only if the fraction is a unit of the domain”. Eight results including
  the single-DVR `addVal_eq_zero_iff`, fractional ideals and unique-factorization facts;
  none states this node.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf/RingTheory` and
  `dag/lean_names_upstream.json` for `WeilHeightOnePrime`, `weilFractionOrder`,
  `principalDivisor`, `WeilDivisor`, and the item id found the existing divisor and
  fraction-order modules plus consumers, but no principal-divisor kernel statement.

No statement dispute or mathematical fault found.

## Second reading by Q48

A separate clause-by-clause rereading of the node and completed file was performed by
this worker; no second agent was started, as the dispatcher explicitly forbids it.
The table above records that audit. The normalization quantifies over all local units,
all uniformizers and every integer power, including negative powers. The local inclusion
is a concrete specialization of Mathlib's localization map. Both directions of each
membership criterion and of the kernel are present. The homomorphism coordinates use
the same existing fraction order as the downstream boundary-clearing theorem. The field
clause is explicit. The additive wrapper changes only notation for the domain group.
The first compiler pass required explicit denominator monoids in `IsLocalization.map`;
this elaboration fix changed no mathematical clause. No additional hypothesis or missing
clause was found on rereading.
