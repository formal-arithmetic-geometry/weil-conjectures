## Worker report

The module `Sheaf.RingTheory.MinimalPrimeFiniteTypeFiniteAway` states
`RingHom.exists_finite_awayMap_of_finite_fiber_minimalPrime` with a `sorry` proof.
It defines no new notions and changes only the item's `lean` record.

Clause-by-clause correspondence:
- Commutative rings R and S: `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`.
  The independent explicit universes cover arbitrary sizes of both rings.
- The given homomorphism: `(φ : R →+* S)`.
- Finitely generated R-algebra: `(hφ : φ.FiniteType)`. In Mathlib this is precisely
  `@Algebra.FiniteType R S _ _ φ.toAlgebra`, so the structure is induced by φ.
- Minimal prime p, including primality: `(p : Ideal R) (hp : p ∈ minimalPrimes R)`.
  `minimalPrimes R` means minimal primes over the zero ideal; its membership includes
  primality and absence of a strictly smaller prime, without any reducedness hypothesis.
- Finitely many primes of S contracting to p:
  `(hfinite : {q : PrimeSpectrum S | Ideal.comap φ q.asIdeal = p}.Finite)`.
  `PrimeSpectrum S` bundles exactly a prime ideal and its primality proof, so this counts
  precisely the prime ideals in the node, and does not assume the fibre is nonempty.
- An element g of R outside p: `∃ g : R, g ∉ p ∧ ...`.
- Finitely generated module over the specified localizations via the induced map:
  `(Localization.awayMap φ g).Finite`. The map has domain `Localization.Away g`
  and codomain `Localization.Away (φ g)`. `RingHom.Finite` means `Module.Finite` with
  the algebra/module structure induced by that exact map. No unrelated scalar action
  is selected, and no integral-domain, reducedness, injectivity or Noetherian assumption
  is imposed.

Dependency declarations read and used:
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, `RingHom.FiniteType`
  (def-weil-pbc-finite-type-algebra).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, `RingHom.Finite`
  (def-weil-finitely-generated-module).
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, the localization
  at `Submonoid.powers g`; used through `Mathlib.RingTheory.Localization.Away.Basic`,
  which also supplies `Localization.awayMap` (def-weil-ring-localization-away).
- `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`: `minimalPrimes`, `IsMinimalPrime`,
  `Ideal.IsMinimalPrime`; `Mathlib.RingTheory.Spectrum.Prime.Defs`: `PrimeSpectrum`.

The recorded modules of stated proof dependencies are imported without `public`:
`Sheaf.RingTheory.FiniteTypeAlgebraFiniteSpectrum` (`Algebra.finiteType_finiteSpectrum`),
`Mathlib.RingTheory.LocalRing.ResidueField.Fiber` (the fibre-prime order isomorphism and
fibre/localization quotient), `Mathlib.RingTheory.Localization.AtPrime.Basic`,
`Mathlib.RingTheory.KrullDimension.Zero` (minimal-prime localization dimension zero),
`Mathlib.RingTheory.Ideal.Maps` and `Mathlib.RingTheory.Nilpotent.Lemmas` (nilpotence
of extended ideals). The declaration docstring carries all six proof steps of the node.

Source checked: `literature/stacks-project/algebra.tex`, lines 30417 onward,
`lemma-generically-finite`, Tag 02ML. Its hypotheses and conclusion agree exactly with
this node. There is no statement correction and no disputed statement.

Edge cases checked: the base zero ring has no minimal prime, so no instance of the
hypotheses; a zero target ring has empty fibre and is a finite zero module, with g = 1.
Empty fibres are allowed, including when localization makes the target zero. Nonreduced
bases are allowed: the source uses nilpotence in the minimal-prime localization, not
reducedness. Zero algebra generators give the empty spanning monomial 1, and denominator
products can be empty (equal to 1). No characteristic restriction occurs. The finiteness
hypothesis is on the set of primes, not the set of elements of the fibre algebra.

Searches for an existing statement (2026-10-15):
- `msearch.py ... leanfinder "A finite type algebra with finite fibre over a minimal prime
  becomes a finite module after localization away from that prime"`: eight hits, including
  `Algebra.QuasiFiniteAt`, preservation of finiteness under localization, and local module
  finiteness criteria. None states existence of the desired principal neighbourhood.
- `msearch.py ... loogle '\"FiniteType\", \"Away\", \"Finite\"'`: four hits, on finite-type
  localization preservation; none is the node's assertion.
- `msearch.py ... leansearch "finite type algebra finite fiber minimal prime finite
  localization"`: unavailable (Internal Server Error); no verdict inferred.
- `msearch.py ... grep 'generically.*finite|exists.*finite.*(away|localiz)|finite.*minimal'
  RingTheory`: sixteen hits. Read `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`
  in `Mathlib.RingTheory.Etale.QuasiFinite`; it assumes an integral intermediate algebra,
  a localized surjection and a fibre unit, and does not state this lemma.
- `rg` with the same pattern in the upstream `WeilConjectures` and project `lean/Sheaf`:
  hits include Noether normalization and other finite-localization criteria. Read the
  upstream `Algebra.FiniteType.exists_finite_aeval_away`: it assumes a domain and supplies
  polynomial coordinates; it is not this statement. The project's finite-localization
  results likewise have different input hypotheses. No exact statement found.
- `grep -rn` for the item's id in upstream `WeilConjectures`: no hits.
- `rg` in `dag/lean_names_upstream.json` for minimal primes / finite-away names: only
  Noether normalization and unrelated graded localization names.
- `rg` for the proposed declaration name in Mathlib, upstream and project source:
  no existing declaration found.

Validation: server compilation via `scompile.py` and delivery dry run via
`deliver2.py --no-push` are run for this delivery; their results are recorded below.

Server compile passed cleanly (1.1 seconds, nice 19, two threads, 60-second file limit).
The delivery dry run printed OK: compiles and passes preflight except for the independent
second reading, which is reserved for the next worker. Nothing was pushed.


## Second reading by NC

Independent second reader, 2026-10-15. Read the node, the sandbox module, all three
statement-dependency nodes and the actual Mathlib declarations they record. Read
`algebra.tex`, Conventions (rings are commutative with identity, including the zero
ring; contraction notation does not require injectivity), and Tag 02ML,
`lemma-generically-finite`. No additional standing hypotheses occur there.
The node agrees with that source, so no statement correction is needed.

The complete object/hypothesis/conclusion checklist is:

1. Objects R and S, commutative rings: `{R : Type u} {S : Type v}` and
   `[CommRing R] [CommRing S]`. Exact; neither ring is assumed a domain,
   reduced, Noetherian, or nonzero. Both universes are explicitly bound.
2. Given ring homomorphism R → S: `(φ : R →+* S)`. Exact; neither injectivity
   nor surjectivity is required. There is no independent algebra instance.
3. S is generated by finitely many elements as an R-algebra through φ:
   `(hφ : φ.FiniteType)`. Exact: `RingHom.FiniteType` unfolds to
   `@Algebra.FiniteType R S _ _ φ.toAlgebra`, whose `out` says the top
   subalgebra is finitely generated. This is the dependency's recorded notion,
   with the algebra structure selected by the given map.
4. A minimal prime ideal p of R: `(p : Ideal R) (hp : p ∈ minimalPrimes R)`.
   Exact: membership unfolds to `(⊥ : Ideal R).IsMinimalPrime p`, namely
   minimality among prime ideals containing zero. It includes primality.
5. Finitely many prime ideals q of S with contraction p:
   `(hfinite : {q : PrimeSpectrum S | Ideal.comap φ q.asIdeal = p}.Finite)`.
   Exact: `PrimeSpectrum` has fields `asIdeal` and `isPrime`; proof irrelevance
   ensures the bundled primes count exactly the ideals. `Ideal.comap` is
   inverse image along φ. This hypothesis does not require a nonempty fibre
   or finiteness of the set of elements of a fibre ring.
6. There exists g in R outside p: `∃ g : R, g ∉ p ∧ ...`. Exact, with g chosen
   after the rings, map, p and hypotheses, and one common g for the conclusion.
7. The specified localization S_{φ(g)} is a finitely generated R_g-module
   through the induced ring map: `(Localization.awayMap φ g).Finite`.
   Exact: read `Localization.awayMap` in Away/Basic.lean: its domain is
   `Localization.Away g`, codomain `Localization.Away (φ g)`, and its value
   is `IsLocalization.Away.map _ _ φ g`. These are the dependency's
   localizations at the powers of the indicated elements. Read
   `RingHom.Finite` in Finiteness/Defs.lean: it uses the map's `toAlgebra`
   and `Module.Finite` (the dependency's finite generation of the top
   submodule). Thus no unrelated module action or cardinal finiteness is used.

Edge cases: the zero base ring has no prime ideal, hence cannot supply hp;
this is precisely the source's vacuous case. The zero target is allowed and
has empty fibre; its localizations are zero modules, finite over the base
localizations (g = 1 is outside any prime). Empty fibres for nonzero targets
are likewise permitted. Finitely many algebra generators includes zero
 generators, and the proof docstring explicitly retains the empty monomial 1
and empty denominator products. Nonreduced bases are retained; the proof
uses local nilpotence at a minimal prime rather than reducedness. There is
no characteristic restriction. Independent `u v` cover arbitrary ring sizes;
there is no test-object quantifier that could become vacuous in a small
universe. Scheme and index-set edge cases do not add objects to this ring lemma.

Independent H4 searches, using queries different from the first reader:

- LeanFinder through `msearch.py`: "finite type ring homomorphism finite after
  inverting an element outside a minimal prime whose fiber has finite spectrum".
  Eight results. `Algebra.QuasiFiniteAt` is a definition;
  `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` concerns all base
  primes; `RingHom.localization_away_map_finite` preserves preexisting
  finiteness. None states this existence result at one minimal prime.
- Loogle through `msearch.py`: `"minimalPrimes", "Finite"`. Two results,
  `minimalPrimes.finite_of_isNoetherianRing` and
  `Ideal.finite_minimalPrimes_of_isNoetherianRing`, count minimal primes;
  neither provides a finite localization of an algebra.
- LeanSearch through `msearch.py`: "finite type algebra becomes module finite
  near a minimal prime with finitely many primes lying over it". Service
  unavailable (Internal Server Error); no mathematical verdict inferred.
- `rg` in Mathlib RingTheory, upstream `WeilConjectures` and project
  `lean/Sheaf`, with `generically.finite`, minimal/finite/away combinations,
  `exists.*finite.*away`, `exists.*finite.*localiz`, and principal finiteness.
  Opened `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`:
  it requires an integral intermediate algebra, a localized surjection and
  a fibre unit. Opened upstream `Algebra.FiniteType.exists_finite_aeval_away`:
  it requires a domain and gives polynomial normalization coordinates.
  Opened project `Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime`,
  `Algebra.FiniteType.exists_finite_subalgebra_away`, and
  `exists_finite_away_maximal_localization`: they concern a finite subalgebra
  after source localization, domain normalization, or localization of an already
  finite map at a maximal ideal. None is this lemma. No duplicate found.

H8 and proof imports: compared all six node proof steps with the declaration
 docstring: fibre-prime correspondence and finite spectrum; monic coefficient
lifting; nilpotence; coefficient denominators and equality annihilators;
the common g and monic equations; bounded monomials spanning the module.
Each step and its cited nodes is retained. Read the recorded proof-dependency
signatures and the project's `Algebra.finiteType_finiteSpectrum`; its general
field/algebra universes, zero-ring allowance, and module finiteness conclusion
are usable here. All recorded statement and stated proof-dependency modules
are imported, with proof-only imports nonpublic. There are no new definition
nodes or delivered dependency modules to audit, and no hollow definitions,
private copies, new axioms, or proved auxiliary facts. The sole proof is `sorry`.

Mismatches found: none. Changes: appended this independent review only; retained
the correct Lean module and node. Checked `lean.statement` verbatim against the
file's signature, all variables/universes bound, and every Lean line at most
100 characters. Server `scompile.py` passed cleanly for the sole delivered file:
1.2 seconds, nice 19, two threads, 60 seconds per file. Delivery dry run and push
follow this review.
