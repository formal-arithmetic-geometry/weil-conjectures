## Worker report

`Sheaf.RingTheory.UniversallyCatenaryMinimalQuotients` states
`isUniversallyCatenary_iff_quotient_minimalPrimes`, with its only proof `sorry`.
I read Stacks Project `algebra.tex`, `lemma-catenary-check-irreducible`, Tag 0AUP,
clause (2), and the catenary and universally catenary definitions, Tags 00NI and
00NL. The theorem says exactly that clause. No node statement, dependency list,
or proof plan changes. The earlier module was removed as dead; fresh searches
confirmed that its declaration survives nowhere in the current Lean sources.

Each hypothesis and clause has the following Lean rendering:

- The commutative ring A is `(A : Type u) [CommRing A]`, with `universe u`
  explicitly declared and `autoImplicit false`.
- The assumption that A is Noetherian is `[IsNoetherianRing A]`.
- Universal catenarity of A is `IsUniversallyCatenary A` on the left.
- “If and only if” is `↔`; both implications are retained.
- “For every minimal prime ideal p of A” is
  `∀ p : Ideal A, p ∈ minimalPrimes A →`.
  Mathlib's `minimalPrimes` is the set of primes minimal over the zero ideal,
  equivalently minimal among all prime ideals; the entire ideal is quantified.
- “A/p is universally catenary” is `IsUniversallyCatenary (A ⧸ p)`.
  The quotient is the actual ideal quotient, without any choice of component.

Dependencies and the full signatures/docstrings read:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, an abbreviation for `IsNoetherian A A`.
  Its docstring and `isNoetherianRing_iff_ideal_fg` give exactly finite generation
  of every ideal. Its recorded module is publicly imported.
- `def-exc-excellent-ring`: the recorded declaration `IsUniversallyCatenary` in
  `Sheaf.RingTheory.ExcellentRing` is publicly imported and used unchanged.
  It is `IsNoetherianRing R ∧ ∀ (A : Type u) [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A], IsCatenaryRing A`. I read that whole module, including
  `IsPrimeChain`, `IsSaturatedPrimeChain`, `IsCatenaryRing`, `IsQuasiExcellent`
  and `IsExcellent`. The catenary predicate has both the finite bound on all
  chain lengths and equality of saturated-chain lengths. The upstream
  `WeilConjectures.RingTheory.Excellent` also has these global names with a
  different chain encoding; I read it but do not import it alongside the
  dependency's recorded module, which would create duplicate declarations.
- Mathlib `minimalPrimes` in
  `Mathlib.RingTheory.Ideal.MinimalPrime.Basic` supplies the minimal-prime notion;
  this module is publicly imported. Its theorem `Ideal.exists_minimalPrimes_le`
  states that a prime containing an ideal contains a prime minimal over that
  ideal, exactly the proof leaf `lem-weil-pbc-prime-contains-minimal-prime`.
- Proof dependency `def-weil-pbc-finite-type-algebra` records `RingHom.FiniteType`
  in `Mathlib.RingTheory.FiniteType`. I read it and `Algebra.FiniteType`:
  the ring-map predicate uses the algebra structure induced by the map, and the
  algebra predicate is finite generation of the top subalgebra. The module is
  imported without `public` for the proof plan.
- Proof dependency `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus` records
  `PrimeSpectrum.isClosedEmbedding_comap_of_surjective` in
  `Mathlib.RingTheory.Spectrum.Prime.Topology` and
  `PrimeSpectrum.range_comap_of_surjective` in
  `Mathlib.RingTheory.Spectrum.Prime.RingHom`. I read their signatures and source:
  a surjective ring map gives a closed embedding of spectra, whose range is the
  zero locus of its kernel. The Topology module imports RingHom and is imported
  without `public` for this proof dependency.
- Proof dependency `lem-per-universal-catenarity-quotient` has no current Lean
  record or Mathlib match. Its node statement was read; it is cited in the
  natural-language proof docstring. It is unnecessary for elaborating this
  statement, so no additional module or theorem is introduced for it.

The theorem docstring carries all five DAG proof steps: universal catenarity
passes to quotients; choose a minimal prime under the contraction of the lower
endpoint of a prime interval in a finite type algebra B; form B/pB and reduce
finite generators to obtain a finite type A/p-algebra; identify its prime interval
by the quotient spectrum correspondence; and transfer strict chain lengths,
saturation, finite bounds and equal lengths back to B. Nothing is proved.

Edge cases checked before writing:

- The zero ring is included: no `Nontrivial` assumption. It has no primes, so
  the right side is vacuous; any unital algebra over it is also the zero ring
  and has vacuous catenarity.
- For a domain, the only minimal prime is zero, so the criterion has the expected
  quotient-by-zero case. Neither domain nor reducedness is assumed.
- Nonreduced rings such as k[e]/(e²), and rings with several minimal primes such
  as k[x,y]/(xy), remain included. Every minimal prime is tested, without
  requiring the components to be disjoint.
- Equal endpoints in the proof's intervals allow length-zero chains. No finite
  dimension bound, localness, characteristic condition, or nonempty spectrum
  is imposed.
- A and its ideal quotient live in the same arbitrary explicit universe u. The
  existing universal-catenarity definition tests algebras in the base universe;
  finite type algebras admit polynomial-quotient representatives in that
  universe, as the upstream Excellent module also explains. No independent
  lower test-algebra universe or universe equality is added to the theorem.

Fresh searches run with `msearch.py Q120
lem-per-universal-catenarity-minimal-quotients`:

- `leanfinder`, query “A Noetherian ring is universally catenary if and only if
  every quotient by a minimal prime ideal is universally catenary”: eight hits,
  including `minimalPrimes.finite_of_isNoetherianRing`,
  `Ideal.finite_minimalPrimes_of_isNoetherianRing`, height results and
  `Ideal.isLasker`; none states the criterion.
- `loogle`, query `"catenary"`: zero hits.
- `grep`, query `catenar|Catenar`, subdirectory `RingTheory`: zero Mathlib hits.
- `leansearch`, query “Universal catenarity of a Noetherian ring is equivalent
  to universal catenarity of every minimal prime quotient”: eight hits,
  including `minimalPrimes`, Noetherian criteria and
  `isStronglyTranscendental_mk_of_mem_minimalPrimes`; none states the criterion.
- Direct `rg` for `catenar|Catenar` in `lean/WeilConjectures` found the Excellent
  definitions and their finite-type permanence theorem, not this equivalence.
  A separate item-id search there found nothing.
- Direct `rg` for `IsUniversallyCatenary` and the selected declaration name in
  `lean/Sheaf` found the recorded definition, dimension formulas, regular and
  Cohen--Macaulay ring results, weakly etale results and affine-cover criteria,
  but no minimal-prime-quotient equivalence. The exact declaration name is also
  absent from `dag/lean_names_upstream.json`.

There are no new nodes, dependency repairs, source discrepancies or statement
corrections. No `STATEMENT-DISPUTED` issue was found. The only changed node field
is `lean`, whose signature is copied verbatim from the theorem. An initial
read-only Git status/history query was a process deviation from the brief;
no direct Git mutation or read-clone edit was made. All compilation and delivery
use only the prescribed wrappers.

## Second reading by Q120

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
