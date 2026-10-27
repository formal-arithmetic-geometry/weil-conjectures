## Worker report

The module `Sheaf.RingTheory.BirationalGenericLocalization` states
`Localization.bijective_map_of_unique_minimalPrimes`, with `sorry` as its entire proof.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.
The docstring contains all seven steps of the accepted node proof and identifies the
localization prime correspondence, minimal-prime existence, and maximal-ideal inputs.

Source checked: literature/stacks-project/morphisms.tex, lemma-birational-generic-fibres
(Tag 0BAB), affine-ring paragraph at lines 13031–13047. It assumes precisely the unique
minimal primes, contraction identity, and generic local-ring isomorphism used here.
No reducedness, Noetherianity, finite type, or finite presentation is required.

Clause-by-clause translation:

- Commutative rings B and A: `{B : Type u} {A : Type v} [CommRing B] [CommRing A]`.
  The universes are independent and explicitly declared.
- The given unital ring homomorphism: `(φ : B →+* A)`.
- The specified primes: `(q : Ideal B) (p : Ideal A) [q.IsPrime] [p.IsPrime]`.
  The instance binders express the primality already present in the node, and allow
  use of Mathlib's `primeCompl` and `Localization.AtPrime`.
- B has unique minimal prime q: `(hB : minimalPrimes B = {q})`.
- A has unique minimal prime p: `(hA : minimalPrimes A = {p})`.
  Mathlib's `minimalPrimes R` consists of primes minimal over zero, equivalently primes
  containing no strictly smaller prime; the singleton equalities express both existence
  and uniqueness, not just at-most-one.
- The contraction identity: `(hpq : q = p.comap φ)`. Equality is symmetric, so this
  is exactly the stated φ⁻¹(p) = q, oriented for the existing canonical-map API.
- B_q and A_p: `Localization.AtPrime q` and `Localization.AtPrime p`.
- The hypothesis on the specified generic map:
  `(h : Function.Bijective (Localization.localRingHom q p φ hpq))`.
  For a ring homomorphism, bijectivity is precisely being an isomorphism. This tests
  the specified fraction map, not the existence of some ring isomorphism.
- A_q: `Localization (q.primeCompl.map φ)`, i.e. localization of A at the image
  of the multiplicative subset B minus q. This does not use a complement of a
  different prime of A.
- The conclusion is `Function.Bijective` of
  `IsLocalization.map (S := Localization.AtPrime q)
    (Localization (q.primeCompl.map φ)) φ (Submonoid.le_comap_map q.primeCompl)`.
  The last argument is Mathlib's denominator-inclusion theorem, not an extra
  hypothesis. `IsLocalization.map_mk'` identifies its value on b/s with φ(b)/φ(s).

Dependencies and existing interfaces read:

- `def-weil-pbc-localization-at-prime`: Mathlib.RingTheory.Localization.AtPrime.Basic,
  `Localization.AtPrime`; inspected its quotient-localization definition and docstring.
  The same record also names `Ideal.ResidueField` and `Ideal.Fiber`; their definitions
  were read in Mathlib.RingTheory.LocalRing.ResidueField.Ideal and .Fiber. Neither
  residue fields nor fibre rings occur in this theorem's signature.
- `lem-weil-pbc-spec-irreducible-components-minimal-primes`: its mathlib_match is
  `PrimeSpectrum.zeroLocus_minimalPrimes` in Mathlib.RingTheory.Spectrum.Prime.Topology.
  Read that signature and the definitions `minimalPrimes`, `IsMinimalPrime`, and
  `Ideal.IsMinimalPrime` in Mathlib.RingTheory.Ideal.MinimalPrime.Basic. This theorem
  uses the minimal-prime notion certified by that dependency; no new copy is defined.
- `Localization.localRingHom` in Mathlib.RingTheory.Localization.AtPrime.Basic:
  read its signature, docstring and definition through `IsLocalization.map`, and
  its `localRingHom_mk'` fraction formula.
- `IsLocalization.map` in Mathlib.RingTheory.Localization.Defs: read its signature,
  docstring, definition and `map_mk'` formula. It supplies the canonical conclusion map.
- Proof dependency `lem-weil-pbc-localization-prime-residue-field-iso`:
  `IsLocalization.prime_localRing_residueField_iso`, imported privately from its
  recorded module WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso;
  its full declaration and proof docstring were read.
- Proof dependencies `lem-weil-pbc-prime-contains-minimal-prime` and
  `lem-weil-pbc-proper-ideal-contained-in-maximal`: `Ideal.exists_minimalPrimes_le`
  in Mathlib.RingTheory.Ideal.MinimalPrime.Basic and `Ideal.exists_le_maximal`
  in Mathlib.RingTheory.Ideal.Maximal. Both full signatures were inspected;
  their modules are plain proof imports.

Edge cases checked before writing:

- The zero ring has no prime ideals, so neither input can be the zero ring under
  the actual hypotheses. No independent Nontrivial hypothesis is added.
- Fields with q = p = zero reduce to the given bijective map; the complements
  and both localizations have the expected form.
- Nilpotents are allowed: the identity of k[ε]/(ε²), which has a unique minimal
  prime, satisfies the hypotheses. There is no domain or reducedness assumption.
- The inclusion k[t] → k[t,t⁻¹], at the zero primes, gives the expected common
  fraction field after base localization; the original ring map need not be bijective.
- The map k[t] → k[t,ε]/(ε²,tε) also becomes an isomorphism after localization at
  the generic prime, since t becomes invertible and kills ε. The statement allows this.
- No injectivity of φ or inequality between u and v is assumed.

Searches for an existing statement (all through the prescribed msearch.py unless noted):

- LeanFinder: “A ring map with unique minimal primes and isomorphic generic local
  rings induces an isomorphism after localizing the target at the image of the
  complement of the source minimal prime”. Eight results. Nearby hits include
  `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes`,
  `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`, and
  `bijective_of_isLocalization_isMaximal`; none states the conclusion from these hypotheses.
- Loogle: `Localization.localRingHom, Function.Bijective`. Three results:
  `Localization.localRingHom_bijective_of_saturated_inf_eq_top`,
  `Localization.exists_awayMap_bijective_of_localRingHom_bijective`, and
  `Localization.localRingHom_bijective_of_not_conductor_le`. They use saturation,
  finiteness/kernel, or conductor hypotheses absent here, respectively.
- Mathlib grep: `generic_localization|[Bb]irational|unique.*[Mm]inimal` in RingTheory.
  One hit, the description of `Localization.AtPrime.prime_unique_of_minimal`,
  about primes of a single localization, not this map.
- LeanSearch: “A homomorphism of commutative rings with unique minimal primes and
  bijective generic local ring map has bijective map after localization at the
  source minimal prime”. Eight results, including `IsLocalization.bijective` and
  localization-local bijectivity criteria. They do not supply this statement:
  in particular `IsLocalization.bijective` already requires the two rings to be
  localizations of the same base at the same denominator set.
- Direct rg over lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json:
  `generic_localization|birational_generic|genericLocalization|lem-sfb-birational-generic-localization`.
  Only an unrelated vertical-fibre theorem and the intended consumer
  BirationalCommonDenseOpens docstring appeared. The chosen full declaration name
  was also searched throughout Mathlib, upstream, Sheaf, and the name index, with no match.

Validation: prescribed scompile.py compiled both sandbox and final library-path forms
successfully, in 1.1 seconds each, without errors or warnings. No disputed statement
or node fault was found. The node copy changes only `lean`.

## Second reading by Q128

A separate final pass by the same worker compared the node, source paragraph and
completed file. No second agent was started, in accordance with the dispatcher's
explicit instruction; the maintainer supplies the independent review.

The final pass checked both singleton minimal-prime hypotheses, the orientation of
contraction equality, the two specified fraction maps, and the distinction between
localization at p and localization at the image of B minus q. It confirmed that
bijectivity is asserted of the canonical map itself, that no finiteness, reducedness,
or algebra-structure hypothesis was introduced, and that both universes are explicit.
No mismatch was found and no statement change was made.
