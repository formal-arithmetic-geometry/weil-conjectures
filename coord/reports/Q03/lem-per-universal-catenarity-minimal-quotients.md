## Worker report

The module `Sheaf.RingTheory.UniversallyCatenaryMinimalQuotients` states
`isUniversallyCatenary_iff_quotient_minimalPrimes`, with `sorry` as its proof.
It is exactly Stacks Project, Algebra, Tag 0AUP,
`lemma-catenary-check-irreducible`, clause (2), read in
`literature/stacks-project/algebra.tex`. The definition of universal catenarity
was also checked against Tag 00NL in that file. No node statement changed.

Clause and hypothesis correspondence:

- A commutative ring A: `(A : Type u) [CommRing A]`, with explicit universe `u`.
- A is Noetherian: `[IsNoetherianRing A]`.
- A is universally catenary: the left side `IsUniversallyCatenary A`.
- If and only if: `↔`, retaining both directions.
- Every minimal prime ideal p of A: `∀ p : Ideal A, p ∈ minimalPrimes A →`.
  Mathlib defines `minimalPrimes A` as the ideals minimal among prime ideals,
  equivalently the minimal primes over the zero ideal.
- The quotient A/p is universally catenary:
  `IsUniversallyCatenary (A ⧸ p)` on the right side.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, the abbreviation for Noetherianity
  of the ring as a module over itself. `isNoetherianRing_iff_ideal_fg` confirms
  exactly that every ideal is finitely generated. Public import retained.
- `def-exc-excellent-ring`: `IsUniversallyCatenary` in
  `Sheaf.RingTheory.ExcellentRing`, one of that node's recorded declarations.
  Its complete definition is Noetherianity and catenarity of every finite type
  algebra. `IsPrimeChain`, `IsSaturatedPrimeChain` and `IsCatenaryRing` in the
  same module encode both finite bounds and equality of saturated chain lengths.
  The existing definition is used without alteration. Public import retained.
- Mathlib `minimalPrimes` and `Ideal.exists_minimalPrimes_le` in
  `Mathlib.RingTheory.Ideal.MinimalPrime.Basic` supply minimal prime ideals
  and the recorded proof leaf `lem-weil-pbc-prime-contains-minimal-prime`.
- Proof dependency `def-weil-pbc-finite-type-algebra` is recorded as
  `RingHom.FiniteType` in `Mathlib.RingTheory.FiniteType`, with
  `Algebra.FiniteType` the corresponding instance-based notion. The proof
  imports that module without `public`.
- Proof dependency `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus` has
  Mathlib matches `PrimeSpectrum.isClosedEmbedding_comap_of_surjective` and
  `PrimeSpectrum.range_comap_of_surjective`; their source signatures were read
  in `Mathlib.RingTheory.Spectrum.Prime.Topology` and
  `Mathlib.RingTheory.Spectrum.Prime.RingHom`. The Topology module is imported
  without `public` for this proof plan.
- `lem-per-universal-catenarity-quotient` has no recorded Lean declaration or
  Mathlib match at this delivery's start, so there is no module to import for
  that proof dependency. It is named in the natural-language proof docstring.
  It is unnecessary to elaborate the statement, and is not restated here.

The theorem docstring gives all five DAG proof steps: passage to quotients;
a minimal prime under the contracted lower endpoint of a prime interval;
finite generation of B/pB over A/p; the quotient prime-interval correspondence;
and transfer of finite bounds, lengths and saturation. No proof is supplied.

Edge cases checked before writing:

- The zero ring is allowed: no `Nontrivial` assumption. It has no prime ideals,
  so the right side is vacuous; any unital algebra over it is again the zero
  ring, making universal catenarity hold as well.
- For a domain the unique minimal prime is zero, giving the expected criterion
  for the quotient by zero; no domain or reducedness is assumed in the theorem.
- A nonreduced ring such as k[e]/(e²) is included, as is the ring k[x,y]/(xy)
  with multiple minimal primes. The quantifier requires every minimal prime,
  without choosing one component or assuming components disjoint.
- Equal endpoints in the proof's prime intervals admit the length-zero chain;
  the statement imposes no strictness condition or dimension bound.
- The universe `u` is explicit, and the quotient remains in `Type u`. No
  independent test-algebra universe, finite-dimension assumption, characteristic
  restriction, or extra localization assumption is introduced.

Searches made using `msearch.py Q03 lem-per-universal-catenarity-minimal-quotients`:

- `leanfinder`: "A Noetherian ring is universally catenary if and only if its
  quotients by all minimal prime ideals are universally catenary". Eight hits,
  including `minimalPrimes.finite_of_isNoetherianRing`,
  `Ideal.finite_minimalPrimes_of_isNoetherianRing` and `Ideal.isLasker`;
  none states this equivalence.
- `loogle`: `"catenary"`. Zero hits.
- `grep`: `catenar|Catenar` in `RingTheory`. Zero Mathlib hits.
- `leansearch`: "Universal catenarity is equivalent to universal catenarity
  of the quotients by all minimal primes of a Noetherian ring". Eight hits,
  including `minimalPrimes`, `Ideal.mem_minimalPrimes_sup` and
  `Ideal.Quotient.isNoetherianRing`; none states the equivalence.
- Direct `rg` of `catenar|Catenar` in `WeilConjectures` and a separate item-id
  search there found no declaration. `rg` of `catenar|Catenar` in `lean/Sheaf`
  found the existing ExcellentRing definitions and different results about
  regular rings, weakly etale maps, affine covers and dimension formulas, but
  no minimal-prime-quotient equivalence. The chosen declaration name also has
  no upstream-name-table attachment.

No new notions or dependency repair modules are needed. No statement dispute
or source mismatch was found. Compilation and delivery preflight use only the
prescribed single-file wrappers.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
