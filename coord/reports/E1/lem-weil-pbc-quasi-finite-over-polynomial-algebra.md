## Worker report

The module `Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra` states the Stacks Project
Tag 00QE result. It binds commutative rings `R,S`, an `R`-algebra structure and
`Algebra.FiniteType R S`, a prime `q`, a natural number `n`, and the equality of the
fibre spectrum's local Krull dimension with `n`. The fibre point is rendered by
`PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S)) ⟨q, rfl⟩`, and
the dimension by `topologicalKrullDimAt` with value `(n : WithBot ℕ∞)`.

The conclusion renders the required principal localization as `g : S` with
`hg : g ∉ q.asIdeal`; the polynomial algebra is `MvPolynomial (Fin n) R`; its
`R`-algebra map to `Localization.Away g` is `f`; finite type is the explicit class
witness `hft`; and quasi-finiteness at every prime is
`@Algebra.IsQuasiFiniteAtPrime ... hft q'`. Thus every prime of the localization is
covered, and the definition supplies the isolated fibre-prime condition.

Dependencies used are Mathlib `Algebra.FiniteType`, `Localization.AtPrime`,
`Ideal.Fiber`, `AlgebraicGeometry.Spec`, `MvPolynomial`, and
`Localization.Away`, plus the project declarations `topologicalKrullDimAt`
(module `WeilConjectures.Mathlib.Topology.KrullDimension`) and
`Algebra.IsQuasiFiniteAtPrime` (module `Sheaf.RingTheory.QuasiFiniteAtPrime`).

Edge cases checked: `n = 0` is represented by `Fin 0`; the fibre point is still
well-defined; `g` is required outside `q`, so the localization is nontrivial at the
chosen point; and the explicit finite-type witness avoids relying on an unavailable
instance for the polynomial-to-localization map.

Searches made: `msearch.py ... leanfinder "finite type algebra locally quasi-finite over polynomial ring in dimension of fibre"` found only general Mathlib quasi-finiteness declarations and no construction; `msearch.py ... loogle "RingHom.QuasiFinite, Algebra.IsQuasiFiniteAtPrime, MvPolynomial"` returned no match for the project predicate; and `msearch.py ... grep "quasiFinite|QuasiFinite|topologicalKrullDimAt" Mathlib/RingTheory Mathlib/Topology` found no local relative-dimension normalization theorem. Grep over `WeilConjectures` and `lean/Sheaf` found no existing Tag 00QE statement.

No `STATEMENT-DISPUTED` or node fault.

## Earlier second reading (a previous round; superseded)

The second reading checked the node and module side by side. The binders for the finite type algebra, prime, fibre point, and dimension integer match the node clause by clause. The conclusion uses an element outside the prime, the `Fin n` multivariable polynomial ring, an explicit finite-type witness for the induced algebra structure, and the predicate at every prime of the localization. No mismatch was found.

## Second reading by E1

Read the item's node, all seven statement-dependency nodes and their recorded
signatures, the module, and the actual definitions used. Read Stacks algebra.tex
in the local source copy /home/ubuntu/c1-stacks-review/algebra.tex: conventions
(lines 32–44), relative dimension (31146–31162), Lemma 00QE (31169–31208), and
Definition 00PL (30232–30243). The local tags table identifies 00QE with
algebra-lemma-quasi-finite-over-polynomial-algebra. There are no ambient
Noetherian, domain, injectivity, field, or characteristic hypotheses in this
lemma. The node has no statement_change and the delivery adds no definition
nodes or dependency modules.

Clause-by-clause list and verdicts:

- Objects R and S and their ring map: `(R : Type u) (S : Type v)
  [CommRing R] [CommRing S] [Algebra R S]`. An algebra structure represents
  an arbitrary unital commutative ring map. Exact; independent universes allowed.
- Finite type of that map: `[Algebra.FiniteType R S]`. Read the class in
  Mathlib/RingTheory/FiniteType.lean: its top subalgebra is finitely generated,
  exactly def-weil-pbc-finite-type-algebra. No extra hypothesis.
- Prime q and contracted prime p: `(q : PrimeSpectrum S)` and
  `q.comap (algebraMap R S)`. Exact, with primality included in PrimeSpectrum.
- Fibre F and corresponding prime Q: `(q.comap (algebraMap R S)).asIdeal.Fiber S`
  and `PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S))
  ⟨q, rfl⟩`. Read Ideal.Fiber and the homeomorphism in Mathlib's
  LocalRing/ResidueField/Fiber.lean. F is κ(p) ⊗[R] S, canonically the node's
  tensor product in reversed order; the homeomorphism gives the unique prime
  contracting to q, hence the kernel of the map to κ(q). Exact.
- Spectrum and dimension at that point: the underlying `PrimeSpectrum F`
  has the Zariski topology of Mathlib's `AlgebraicGeometry.Spec` (read its
  definition in Scheme.lean). Read `topologicalKrullDimAt` in
  WeilConjectures/Mathlib/Topology/KrullDimension.lean: the infimum over open
  neighbourhoods of their subspace Krull dimensions. This is the dependency
  def-kun-topological-dimension-at-point, rather than the local ring dimension.
  Exact.
- Integer n ≥ 0 and dimension equality: `(n : ℕ)` and `hdim` equating that
  dimension to `(n : WithBot ℕ∞)`. Exact finite nonnegative dimension hypothesis.
- Element g outside q: `∃ (g : S) (hg : g ∉ q.asIdeal)`. Exact.
- Principal localization S_g: `Localization.Away g`. Read the powers-submonoid
  localization abbreviation and its ring/algebra structures in Mathlib. This
  uses def-weil-ring-localization-away without a private copy. Exact.
- Polynomial algebra and map: `(f : MvPolynomial (Fin n) R →ₐ[R]
  Localization.Away g)`. Read MvPolynomial's AddMonoidAlgebra definition:
  finitely supported monomials, n variables indexed by Fin n. AlgHom ensures
  compatibility with the given R-algebra structures. Exact.
- Finite type of the new map: existential `hft : @Algebra.FiniteType ...
  f.toRingHom.toAlgebra`. It refers to the polynomial-algebra structure induced
  by this very f, rather than any unrelated instance. Exact.
- Quasi-finiteness at every prime: `∀ q' : PrimeSpectrum (Localization.Away g),
  @Algebra.IsQuasiFiniteAtPrime ... f.toRingHom.toAlgebra hft q'`. Read the
  entire landed QuasiFiniteAtPrime.lean dependency: openness of the singleton
  of the corresponding prime in the fibre spectrum. Exact Definition 00PL;
  hft is shared by all q'. Quantifiers g, its outside-prime proof, f, finite
  type, then all primes have exactly the node's order.

Edge cases: Fin 0 admits n = 0 and the polynomial ring with no variables.
There is no imposed Nontrivial instance: zero rings and empty spectra are
excluded only when they cannot supply the hypothesized prime q, exactly as
in Stacks' conventions. That prime ensures a nonempty chosen fibre, and
hg ensures its point survives localization. Every characteristic is permitted.
R : Type u and S : Type v are independent; the tensor product uses their
maximum universe, and there is no quantification over a smaller universe of
algebras. There is no other index set, scheme, or zero object to restrict.

Independent searches with wording different from the first reader, recorded
by msearch.py in searches.jsonl:

- LeanSearch: "A finite type ring map near a prime factors through a polynomial
  ring with number of variables the fibre dimension and a quasi finite ring map".
  The service returned Internal Server Error; no absence verdict inferred.
- Loogle: "MvPolynomial, Algebra.QuasiFinite": successful, zero hits.
- LeanFinder: "Local Noether normalization of a finite type algebra over any
  commutative base ring with fibre dimension n": returned QuasiFiniteAt,
  QuasiFinite, finite-type/Noetherian and localization results, but no such
  construction theorem.
- Mathlib grep: "quasi.?finite.*polynomial|polynomial.*quasi.?finite|
  exists.*quasiFinite|noether.*normal" in RingTheory: found field Noether
  normalization, polynomial quasi-finite-prime lemmas and Zariski main theorem
  material. Opened NoetherNormalization's main statements and the matching
  Zariski main theorem block: neither states this arbitrary-base local
  normalization result.
- rg over WeilConjectures, repository lean/Sheaf and dag/lean_names_upstream.json
  for the polynomial/quasi-finite combinations, full declaration name and
  00QE: only the dimension-bound theorem and the citer
  FibreDimensionBoundedOpenUpstairs.lean, not this construction. Opened the
  recorded dependencies rather than substituting Mathlib's differently
  presented QuasiFiniteAt predicate.

Mismatches and repairs: no semantic mismatch found and the signature is
unchanged, byte-for-byte equal to lean.statement. H8: the old proof docstring
only named four techniques; expanded it to the full four-step node proof,
including basic-open shrinking, denominator rescaling, the finite Artinian
fibre, finite type, and combining the final two localizations, with explicit
DAG references. H9: added the conventional copyright/license/author header,
moved the module docstring immediately after imports, and removed the unused
Polynomial scoped opening. No definitions or proofs were added; the sole
named theorem retains its sorry. No hollow definitions or unbound variables.

Validation: scompile.py compiled the reviewed 82-line module on the server
in 1.4 seconds, exit code 0, with no errors or warnings. Checked all lines
are at most 100 characters and the recorded signature is verbatim unchanged.
