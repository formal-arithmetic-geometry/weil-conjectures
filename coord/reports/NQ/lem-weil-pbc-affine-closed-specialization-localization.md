## Worker report

The module states `AlgebraicGeometry.affineClosedSpecializationLocalization`, with one
`sorry`, and defines no new notion. The original node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`, with arbitrary explicit universe `u`.
- Any ideal: `(I : Ideal A)`, with no finite generation, properness, or other restriction.
- The multiplicative subset of quotient units: `(S : Submonoid A)` with
  `hS : ∀ a : A, a ∈ S ↔ IsUnit (Ideal.Quotient.mk I a)`.
  This names exactly the specified subset, rather than restricting which ideals are allowed:
  the preimage of `IsUnit.submonoid (A ⧸ I)` under the quotient map always supplies it.
- The fraction ring B is the existing `Localization S`, not an unspecified ring. Mathlib's
  construction uses the fraction equivalence relation in the node, including annihilation
  of cross-products by a further denominator. No non-zero-divisor restriction is imposed.
- T and the canonical morphism are `Spec (.of A)` and
  `Spec.map (CommRingCat.ofHom (algebraMap A (Localization S)))`.
- Weak etaleness is the first conjunct, `AlgebraicGeometry.WeaklyEtale` of that morphism.
- Homeomorphism onto the specified subset: `Topology.IsEmbedding` of its underlying map
  together with the equality of its `Set.range` with
  `{p | ∃ q : PrimeSpectrum A, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal}`.
  An embedding is a homeomorphism onto its range with the subspace topology.
  `PrimeSpectrum.comap (algebraMap A (Localization S))` is definitionally the underlying
  function of this `Spec.map`; it sends a prime to the inverse-image ideal.
- C is `{q : PrimeSpectrum A | I ≤ q.asIdeal}`, exactly V(I). The fourth conjunct
  says this set is contained in the range.
- The last conjunct quantifies over every source prime x and produces a source prime y
  with `Specializes x y` and `I ≤ (PrimeSpectrum.comap ... y).asIdeal`. Both points
  are in the localization spectrum, so this is specialization within the source.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`, including their docstrings
  and full signatures. These are public imports.
- `def-weil-weakly-etale-morphism`: its Mathlib match is
  `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`, `AlgebraicGeometry.WeaklyEtale`.
  Read the class: flat morphism and flat diagonal. Public import; no replacement.
- Proof import `WeilConjectures.Mathlib.RingTheory.Etale.Weakly` provides
  `Algebra.WeaklyEtale.of_isLocalization`, the recorded declaration of
  `lem-weil-pbc-localization-ring-weakly-etale`. Read its full signature and docstring.
- Proof import `Sheaf.RingTheory.IndPrincipalZariski`, the recorded module of
  `def-weil-pbc-ind-etale-algebra`, exposes the existing
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff`; read its signature/docstring
  in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology` provides the recorded proof matches
  `PrimeSpectrum.localization_comap_isEmbedding`, `PrimeSpectrum.localization_comap_range`,
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`, and
  `PrimeSpectrum.localization_away_comap_range`. Read the full signatures.
- Proof import `Mathlib.RingTheory.Ideal.Maximal` provides `Ideal.exists_le_maximal`,
  matching `lem-weil-pbc-proper-ideal-contained-in-maximal`; read its signature/docstring.

Source checked: local `proetale.tex`, lemma-localization (Tag 096V), construction of S
and proof of (1), specialized to f=1; local `more-algebra.tex`,
definition-weakly-etale (Tag 092B) and the subsequent sentence on localizations.
The theorem docstring reproduces all five proof steps and their dependency nodes.

Edge cases checked mathematically before writing:

- I = top: A/I is the zero ring, so every element is a unit, S contains zero,
  Localization S is the zero ring, both V(I) and the asserted range are empty.
- A the zero ring: only the preceding case occurs; all point quantifiers are vacuous.
- I = bottom: S is the units, localization is A, C is the whole spectrum, and each
  point specializes to itself.
- An arbitrary infinitely generated ideal is permitted; the properness argument for
  p + I uses one finite ideal-membership witness, never finite generation of I.
- Direction of specialization: p contained in q means p specializes to q; the final
  clause uses `Specializes x y` in precisely that order.

Searches performed (msearch.py, group NQ, this item):

- leanfinder: "Localization at elements invertible modulo an ideal has spectrum the
  generalizations of the closed subset". Eight hits include general localization range,
  localizationMapOfSpecializes, local-ring specialization, and going down. No full match.
- loogle: `PrimeSpectrum, "localization_comap"`. Four hits: injective, embedding,
  inducing, range. These supply the general localization input, not the quotient-unit
  image identification and full combined assertion.
- grep: `isUnit.*[Ss]ubmonoid|[Ss]ubmonoid.*isUnit|range_comap_algebraMap_localization_compl`.
  Hits include `IsUnit.submonoid`, units/non-zero-divisors for Artinian rings, and a
  polynomial localization range-complement theorem. No full match.
- rg in the upstream WeilConjectures tree and project Sheaf tree for
  `closed.*[Ll]ocalization|[Ll]ocalization.*closed|of_isLocalization|weaklyEtale_SpecMap_algebraMap_iff`:
  general localization and weak-etale inputs found; no full statement.
- grep for this node id in upstream WeilConjectures: no match.
- rg for `affineClosedSpecializationLocalization` in the upstream name index and relevant
  source trees: no collision. Quotient/IsUnit search found unrelated uses only.

Validation: the delivered module compiled cleanly with scompile.py on the server,
using nice 19, two threads, 60 seconds per file. The helper also compiled its required
side import `Sheaf.RingTheory.IndPrincipalZariski` in the private overlay. No local
compiler or global build was run. No statement dispute or node correction was needed.


## Second reading by NQ

Independent reader, 2026-10-15. Read the sandbox node, theorem, its dependency
nodes and actual declarations, and the cited Stacks sources before deciding the
verdict. The statement is faithful; no Lean or node correction is required.

Object, hypothesis and conclusion checklist (all pass):

1. Arbitrary commutative ring A: `(A : Type u) [CommRing A]`. The explicit
   `universe u` permits every ring universe, including zero rings. There is no
   field, nontriviality, characteristic, Noetherian or finiteness assumption.
2. Arbitrary ideal I: `(I : Ideal A)`, without properness or finite generation.
3. T = Spec A: the target of `Spec.map (CommRingCat.ofHom (algebraMap A
   (Localization S)))` is `Spec (.of A)`. Read Mathlib's actual `Spec` and
   `Spec.map` definitions: the points are `PrimeSpectrum A` and the map is
   contraction along that same algebraMap. No alternative spectrum is used.
4. C = V(I): `{q : PrimeSpectrum A | I ≤ q.asIdeal}`. The displayed subset
   uses all prime ideals containing I, without restricting to maximal primes.
5. S is exactly the inverse image of quotient units: `(S : Submonoid A)` and
   `(hS : ∀ a : A, a ∈ S ↔ IsUnit (Ideal.Quotient.mk I a))`. This is an
   explicit parameter for a specified object, not an extra substantive
   assumption: `(IsUnit.submonoid (A ⧸ I)).comap (Ideal.Quotient.mk I)` always
   supplies it, and equality of membership determines S uniquely.
6. B = S⁻¹A with the usual fraction equivalence: `Localization S` is Mathlib's
   actual localization construction. Arbitrary zero divisors and zero in S are
   permitted; no fraction-field or regular-denominator assumption occurs.
7. Canonical h: `Spec.map (CommRingCat.ofHom (algebraMap A (Localization S)))`.
   Each remaining conjunct uses `PrimeSpectrum.comap` of this exact ring map.
8. h weakly etale: the first conjunct is `WeaklyEtale` of h. Read the recorded
   Mathlib class: flatness of h and its diagonal, exactly the dependency node.
9. Homeomorphism onto the points specializing to C: the second conjunct is
   `Topology.IsEmbedding` of the contraction map; the third identifies its
   `Set.range` with `{p | ∃ q, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal}`.
   An embedding is a homeomorphism onto its range with the induced topology.
   The existential q is allowed to depend on p. Mathlib's
   `PrimeSpectrum.le_iff_specializes` confirms that the inclusion points in the
   required specialization direction. Neither an open nor closed embedding is
   claimed.
10. Image contains C: the fourth conjunct is the inclusion of precisely the
    set in item 4 in the range of precisely the map in item 7.
11. Every source point specializes within the source to a point over C:
    `∀ x : PrimeSpectrum (Localization S), ∃ y : PrimeSpectrum (Localization S),
    Specializes x y ∧ I ≤ (PrimeSpectrum.comap ... y).asIdeal`. Both quantified
    points have the source topology, and y depends on x. This is neither just
    specialization of their images nor reversed specialization.

Source check: proetale.tex, `lemma-localization` (096V), assumes only a ring
and D(f) intersect V(I), with I arbitrary. At f = 1 the ring of sections is A/I
and the source's S is exactly item 5. No ambient Noetherian or finite-generation
hypothesis appears in that section. more-algebra.tex,
`definition-weakly-etale` (092B), defines flatness of the ring map and tensor
multiplication; its following paragraph explicitly includes localizations.
The extra final specialization clause follows from the embedding and range
clauses, exactly as the node's fifth proof step explains.

Dependency check: opened the two statement dependency nodes and read Mathlib's
`AlgebraicGeometry.Spec`, `Spec.map` and `WeaklyEtale` signatures and bodies.
Also opened all five proof dependency nodes and their recorded source
signatures: `Algebra.WeaklyEtale.of_isLocalization`,
`AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff`,
`PrimeSpectrum.localization_comap_isEmbedding`, `localization_comap_range`,
`Ideal.exists_le_maximal`, `isTopologicalBasis_basic_opens`,
`localization_away_isOpenEmbedding` and `localization_away_comap_range`.
Their parameters admit exactly the ring and localization in this theorem.
The recorded `Sheaf.RingTheory.IndPrincipalZariski` module publicly exposes the
affine weak-etale equivalence; it does not replace the notion with its stronger
principal ind-Zariski predicate. No new node or dependency module is delivered,
so H12/H13 introduce no additional review obligations.

Edge cases: for I = top, quotient units are every element, hence zero belongs
to S and the localization spectrum and C are both empty. The zero ring is
included in that case. For I = bottom, S is the units, the localization is
isomorphic to A, C is the whole spectrum and reflexive specialization suffices.
For infinitely generated I, properness of p + I still follows from a single
witness 1 = a + i. No index-set, integer-degree or characteristic parameter is
present. A and its concrete localization share the arbitrary universe u, so
there is no independent small test-object universe or excluded ring size.

Independent searches (different terms from the first reader):

- msearch leanfinder: "prime ideals below a prime in a zero locus via
  localization at inverse image of units". Eight hits, including
  `Localization.le_comap_primeCompl_iff`, `IsLocalization.AtPrime.orderIsoOfPrime`
  and the localization prime-spectrum order isomorphisms. These concern a
  prime-complement localization or general localization, not this full theorem.
- msearch loogle: `"Specializes", "PrimeSpectrum"`. Two hits:
  `PrimeSpectrum.le_iff_specializes` and `PrimeSpectrum.localizationMapOfSpecializes`.
  Read the former to check direction; neither states the whole assertion.
- msearch leansearch: "spectrum of localization at preimage of quotient units
  generalization hull of a closed set". Service returned Internal Server Error;
  recorded as unavailable, with no mathematical verdict inferred.
- Independent rg searches in Mathlib/RingTheory, upstream WeilConjectures and
  project lean/Sheaf used vanishing/localization, generalization/localization,
  and quotient/units combinations. Opened the useful upstream hits in
  `WeilConjectures.RingTheory.ProEtale.WLocalization.Basic`: definitions
  `Generalization.submonoid`, `Generalization`, `locClosedSubset`, and lemmas
  `range_algebraMap_generalization` and `exists_specializes_zeroLocus_ideal`.
  Also checked their exact group-clone versions and read
  coord/pefw-upstream-framework.md. Those lemmas give individual clauses for
  localization into (A/I)_f, including the f = 1 case, but none declares the
  full combined weak-etale, embedding, range, containment and source
  specialization assertion here. This delivery defines no competing notion:
  it uses Mathlib's `Localization`, `PrimeSpectrum` and scheme `WeaklyEtale`.
- Exact declaration-name and blueprint-id searches in upstream source,
  dag/lean_names_upstream.json and project lean/Sheaf found no duplicate.

H5/H6/H8/H9: there are no new definitions or private objects, and the sole proof
is the named theorem's whole `by sorry`. The theorem docstring carries all five
node proof steps and their dependency names, with source tags and blueprint id;
the module docstring also has its source. All variables/universes are explicitly
bound; every line is at most 100 characters. Programmatically checked that
`lean.statement` is verbatim the signature in the file. No statement correction
or dispute exists. Mismatches found: none. Changes: appended this independent
review only; preserved the worker's module, node and original report.

Second-reader validation: scompile.py passed on the server, with no warnings
or errors. It compiled IndPrincipalZariski separately (1.4 s) and the delivered
module (1.5 s), each at nice 19, two threads and the 60-second file limit.
