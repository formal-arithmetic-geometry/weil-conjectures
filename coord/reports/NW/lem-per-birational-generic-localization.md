## Worker report

The delivery states `Localization.generic_localization_bijective_of_unique_minimalPrimes`
in `Sheaf.RingTheory.BirationalGenericLocalization`. Its only proof is `sorry`.
The module contains no new definitions. The source is Stacks Project Tag 0BAB,
`morphisms.tex`, `lemma-birational-generic-fibres`, the affine-ring paragraph (read
in the local literature). The seven-step proof docstring follows the item's already
reviewed split. No statement correction or dependency repair is needed; the item's
node changes only in `lean`. In particular the Q16-reviewed stage-1 split is preserved.

Each hypothesis and conclusion is rendered as follows:

- Commutative rings B and A: `{B : Type u} {A : Type v} [CommRing B] [CommRing A]`.
  The two universes are independent and explicitly declared.
- The given ring map: `(φ : B →+* A)`, with no injectivity or finiteness assumption.
- Prime ideals q and p: `(q : PrimeSpectrum B) (p : PrimeSpectrum A)`. These are
  Mathlib's bundled prime ideals, with underlying ideals `q.asIdeal` and `p.asIdeal`.
  Their existing primality instances permit use of their prime-complement submonoids.
- q is the unique minimal prime of B: `(hq : minimalPrimes B = {q.asIdeal})`.
  Equality with this singleton asserts both membership and uniqueness.
- p is the unique minimal prime of A: `(hp : minimalPrimes A = {p.asIdeal})`.
  No reducedness or domain assumption is substituted for this condition.
- The inverse image of p is q: `(hqp : q.asIdeal = p.asIdeal.comap φ)`.
  This is the stated equality with its sides reversed, as required by `localRingHom`.
- The induced local-ring map is an isomorphism:
  `(hlocal : Function.Bijective (localRingHom q.asIdeal p.asIdeal φ hqp))`.
  This uses the specific induced map, not an arbitrary isomorphism. A unital ring
  homomorphism is an isomorphism exactly when its underlying function is bijective.
- A_q means localization of A at the image of B minus q:
  `Localization (q.asIdeal.primeCompl.map φ)`.
  `primeCompl` is precisely the multiplicative complement of q; `Submonoid.map`
  gives its image under φ, without replacing the image by the complement of p.
- The conclusion is bijectivity of
  `IsLocalization.map (Localization (q.asIdeal.primeCompl.map φ)) φ
  q.asIdeal.primeCompl.le_comap_map`, explicitly typed as a ring homomorphism from
  `Localization.AtPrime q.asIdeal` to that localization of A. This is the canonical
  map b/s ↦ φ(b)/φ(s), by `IsLocalization.map_mk'`. The submonoid containment proof
  `le_comap_map` is Mathlib's existing theorem, not an extra mathematical hypothesis.

Statement-dependency declarations read and used:

- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`, from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. The full recorded collection also
  contains `Ideal.ResidueField` and `Ideal.Fiber`; their source definitions were read,
  though the statement itself only needs localizations. The canonical map uses
  `IsLocalization.map` from `Mathlib.RingTheory.Localization.Defs`.
- `lem-weil-pbc-spec-irreducible-components-minimal-primes`: its Mathlib match
  `PrimeSpectrum.zeroLocus_minimalPrimes`, from
  `Mathlib.RingTheory.Spectrum.Prime.Topology`. This is imported publicly; it uses
  Mathlib's `minimalPrimes` (minimal primes over zero), which is exactly the notion
  in the hypotheses. No private minimal-prime predicate is introduced.

Proof-dependency imports (ordinary imports, since these are needed for stage 3):

- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`, declaration
  `IsLocalization.prime_localRing_residueField_iso`; its docstring and full signature
  were read. Only clause (1), the localization prime correspondence, is used in the
  paper proof. No dependency repair is required for this use.
- `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`, declaration
  `Ideal.exists_minimalPrimes_le`, the recorded Mathlib match of
  `lem-weil-pbc-prime-contains-minimal-prime`.
- `Mathlib.RingTheory.Ideal.Maximal`, declaration `Ideal.exists_le_maximal`, the
  recorded Mathlib match of `lem-weil-pbc-proper-ideal-contained-in-maximal`.
- The remaining proof dependency is the already public localization module above.

Edge cases checked before writing: a zero ring has no prime ideal, so the bundled
prime binders exclude exactly the impossible case already excluded by the node's
unique-minimal-prime hypothesis. For a field with φ the identity, both primes are
zero and the conclusion is the canonical identity localization isomorphism. For
dual numbers over a field and the identity map, nonreduced rings remain allowed.
For k[t] → k[t,e]/(e²,te), the unique minimal primes are zero and (e); localizing at
nonzero elements of k[t] kills e, so the generic map is an isomorphism without the
target being reduced. For the reverse quotient map, generic localization also kills
e, so the hypotheses and conclusion allow a noninjective original ring map. No
finite-type, finite-presentation, Noetherian, domain, field, or characteristic
assumptions have been added. The theorem has no bound relating the two ring universes.

Searches performed in this session (2026-10-19):

- `msearch.py ... leanfinder`: "A commutative ring map with unique minimal primes
  and isomorphic local rings at those primes induces an isomorphism after localizing
  the target at the source minimal prime". Eight results include
  `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes`,
  `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`,
  `Localization.localRingHom_unique`, and `bijective_of_isLocalization_isMaximal`.
  These concern a localization's spectrum, iterated localization, uniqueness, or
  checking all maximal localizations; none is the item's implication.
- `msearch.py ... loogle`: `Localization.localRingHom, Function.Bijective`.
  Three results: `Localization.localRingHom_bijective_of_saturated_inf_eq_top`,
  `Localization.exists_awayMap_bijective_of_localRingHom_bijective`, and
  `Localization.localRingHom_bijective_of_not_conductor_le`. Their subalgebra
  saturation, module-finiteness, or conductor hypotheses do not match this node.
- `msearch.py ... leansearch`: "A commutative ring map with unique minimal primes
  and isomorphic generic local rings becomes an isomorphism after localizing its
  target at the complement of the source minimal prime". Eight results include
  `Localization.localRingHom`, `IsLocalization.minimalPrimes_comap`, and
  `PrimeSpectrum.localization_specComap_injective`; no exact statement match.
- `msearch.py ... grep`, in `RingTheory/Localization`:
  `unique.*minimal.*prime|birational.*local|subsingleton_primeSpectrum`.
  The only hit is `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes`.
- Direct `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` for
  `generic.*localization|birational.*local|unique.*minimal`, and the narrower
  ring-theory directories, found other generic-localization results but no exact
  statement. A direct upstream `grep -rn` for the item's id found no result.
- The source signatures/docstrings of `Localization.localRingHom`,
  `IsLocalization.map`, `IsLocalization.map_mk'`, `PrimeSpectrum`, `minimalPrimes`,
  and `Submonoid.le_comap_map` were read. No new construction is needed.

Validation: `scompile.py NW lem-per-birational-generic-localization` compiled both
the sandbox and library module successfully (1.4 s and 1.5 s), with no messages.
Every universe and variable is explicitly bound. No `#check`, file-local notation,
local instance, private definition, or postponed data construction occurs.

## Second reading by NW

This is a second pass by the same dispatcher worker; the brief prohibits starting
other agents, and the maintainer supplies the independent review. I reopened the
node and the finished module and checked every binder and conclusion against the
source paragraph. B and A occur in the correct direction; q belongs to B, p to A;
both singleton equations state uniqueness, not just minimality; the contraction
equality has the orientation required by the existing local-ring map; the assumed
isomorphism is on B_q → A_p, while the asserted isomorphism has target the localization
of A at φ(B minus q). In particular those two targets are not conflated in the
statement. The chosen map is the canonical Mathlib map, not an existential witness.
The seven proof steps in the docstring retain the recorded four proof dependencies.
No discrepancy or statement correction was found, and no mathematical fields of the
stage-1 node were changed.
