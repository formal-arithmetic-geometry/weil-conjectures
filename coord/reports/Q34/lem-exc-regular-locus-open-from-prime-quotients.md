## Worker report

The module `Sheaf.RingTheory.RegularLocusOpenFromPrimeQuotients` states
`RingTheory.isOpen_regularLocus_of_primeQuotient_regularOpen`, with one `sorry` and
no other declaration. The node statement and all its other fields are unchanged;
only its `lean` record is supplied. No new nodes or dependency repairs are needed.

Source read: Stacks Tag 07P9, `lemma-intersection-regular-with-closed`, and Tag 07P7,
`definition-J` (https://stacks.math.columbia.edu/tag/07P9 and
https://stacks.math.columbia.edu/tag/07P7). The same TeX definitions and proof were also read in the available local copy
`weil-launcher-nt/literature/stacks-project/more-algebra.tex`, lines 11582–11649.
The source assumes exactly a Noetherian
ring whose every prime quotient is J-0, and concludes J-1. Tag 07P7 expands J-0 as
containing a nonempty regular open, and J-1 as openness of the regular locus.
The theorem docstring gives the seven steps of the DAG proof, with the dependency
identifiers and the denominator-clearing and regular-sequence arguments.

Clause-by-clause correspondence:

- A commutative Noetherian ring is `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`. Its universe `u` is explicitly bound and unrestricted.
- Every prime ideal is `∀ (p : Ideal A), p.IsPrime →`. There is no assumption of
  positive dimension, a field structure, finite type, or nontriviality of `A`.
- An open subset of the spectrum of its prime quotient is
  `∃ U : Set (PrimeSpectrum (A ⧸ p)), IsOpen U ∧ ...`.
- Its nonemptiness is the separate conjunct `U.Nonempty`.
- Every point of that open has regular local ring is
  `∀ q : PrimeSpectrum (A ⧸ p), q ∈ U →
    IsRegularLocalRing (Localization.AtPrime q.asIdeal)`.
  The `PrimeSpectrum` point supplies the primality instance for localization.
- The conclusion is exactly `IsOpen {q : PrimeSpectrum A |
  IsRegularLocalRing (Localization.AtPrime q.asIdeal)}`. No assertion is made
  about points outside that set or about regularity of the ring as a whole.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the abbreviation
  `IsNoetherian A A`; `isNoetherianRing_iff_ideal_fg` identifies it with every
  ideal being finitely generated (source lines 193–207).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, with its
  `Spec.locallyRingedSpaceObj` underlying space; the point space is
  `PrimeSpectrum A`. Only the underlying Zariski topological space is needed by
  this node. The full affine-scheme definition and `Spec.map` were read at
  lines 468–480. That recorded module is publicly imported.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, the
  quotient-type localization at the prime complement (lines 48–58).
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, a local
  Noetherian ring whose maximal ideal spanFinrank equals its Krull dimension
  (lines 48–65). This is the regular-local clause recorded by
  `def-weil-regular-scheme`; no scheme-regularity specialization is needed.

All four recorded statement modules are public imports. The stated proof
modules are imported without `public`: the Mathlib modules for localization
of primes and iterated localization, localization exactness, regular sequences,
closed sets of spectra, regular-sequence localization, quotient localization,
and Noetherian localization, together with
`Sheaf.RingTheory.RegularLocalLocalization` and
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`. Their recorded
statements and source files were read. The three proof prerequisites
`lem-exc-regular-sequence-principal-neighbourhood`,
`lem-exc-regular-local-lift-regular-sequence-quotient`, and
`lem-exc-nagata-principal-open-criterion` have no recorded module on the base;
they are proof prerequisites only, so no new notion is needed to state this item.

Edge cases checked:

- The zero ring has empty prime spectrum. Its universal prime-quotient premise
  is vacuous and its empty regular locus is open; no `[Nontrivial A]` was added.
- For a field, the single prime quotient admits the whole one-point spectrum
  as its nonempty regular open, and the conclusion is the whole spectrum.
- Dimension zero and an empty regular system of parameters are permitted;
  the signature mentions neither a positive dimension nor a nonempty sequence.
- The empty open does not satisfy `U.Nonempty`, as the source requires.
- All quotient and localization rings live in the same arbitrary universe as
  `A`; no auxiliary test-ring universe can make a premise vacuous.

Searches run through the prescribed `msearch.py` wrapper:

- LeanFinder: “A Noetherian ring has open regular locus if every quotient by a
  prime ideal has a nonempty open subset of regular local rings”. Eight hits,
  concerning Noetherianity of spectra and localizations; no matching theorem.
- Loogle: `IsRegularLocalRing, IsOpen`. Zero hits.
- Grep: `regularLocus|regular_locus|JOne|JZero` under `RingTheory`. Eight hits,
  all on graded-ring degree-zero projections, not the required criterion.
- LeanSearch: “Open regular locus from nonempty regular opens in every prime
  quotient”. Eight hits, including the Zariski topology, basic opens, etale and
  unramified loci, and topological regular spaces; none states this criterion.
- Direct `rg` of `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `regularLocus|regular_locus|JOne|JZero`
  and the item id found the different finite-residue-field-model criterion
  in `Sheaf.RingTheory.JTwoResidueFieldCriterion`, whose step 6 cites this item.
  It does not state the prime-quotient criterion. The proposed declaration name
  is absent from the source and Mathlib.

No statement dispute or node fault was found. All compilation uses the required
`scompile.py` wrapper; the final dry run uses `deliver2.py --no-push`. The second
reading is left to the independent second reader, and nothing is pushed.

Validation: `scompile.py Q34 lem-exc-regular-locus-open-from-prime-quotients`
passed for the delivered module, both sandbox and library checks, with no errors
or warnings. The required `deliver2.py --no-push` preflight is the final check.

## Second reading by Q34

I independently read the sandbox node and module, the four statement-dependency
nodes and their actual Mathlib declarations, the proof-dependency records and
available declarations, and the local Stacks TeX at
`/home/ubuntu/weil-launcher-nt/literature/stacks-project/more-algebra.tex`,
section `section-singular-locus`. In particular, `definition-J` (07P7) defines
J-0 and J-1, and `lemma-intersection-regular-with-closed` (07P9) assumes only a
Noetherian ring and J-0 for every prime quotient. The surrounding section adds
no field, reducedness, domain, finite-type, or nonzero-ring assumption.

My object/hypothesis/conclusion inventory and comparison with the Lean is:

1. Object: an arbitrary commutative ring A. Lean: `(A : Type u) [CommRing A]`,
   with `universe u` explicitly declared. Exact; no size restriction or extra
   algebra structure.
2. Hypothesis: A is Noetherian. Lean: `[IsNoetherianRing A]`. Exact: the
   recorded `Mathlib.RingTheory.Noetherian.Defs` abbreviation is `IsNoetherian
   A A`, and `isNoetherianRing_iff_ideal_fg` is the every-ideal-finitely-generated
   criterion of `def-weil-pbc-noetherian-ring`.
3. Quantifier: every prime ideal p of A. Lean: `∀ (p : Ideal A), p.IsPrime →`.
   Exact: no maximality or regularity assumption on p, and the existential
   open is inside this quantifier, so it may depend on p.
4. Object: Spec(A/p), with its Zariski topology. Lean: `PrimeSpectrum (A ⧸ p)`.
   Exact: `AlgebraicGeometry.Spec` in the recorded module has
   `Spec.locallyRingedSpaceObj` as underlying locally ringed space, with this
   underlying Zariski space. No scheme structure is needed in this purely
   topological conclusion; the recorded spectrum module is publicly imported.
5. Hypothesis: a nonempty open subset U_p of that spectrum. Lean:
   `∃ U : Set (PrimeSpectrum (A ⧸ p)), IsOpen U ∧ U.Nonempty ∧ ...`.
   Exact: openness is in the quotient spectrum, not the ambient spectrum;
   nonemptiness is explicit, and no fixed or common open is demanded.
6. Hypothesis: every q in U_p has regular local ring (A/p)_q. Lean:
   `∀ q : PrimeSpectrum (A ⧸ p), q ∈ U →
   IsRegularLocalRing (Localization.AtPrime q.asIdeal)`.
   Exact: q is a prime of the quotient, not a prime of A. The point's prime
   instance supplies the localization. The dependency's
   `Localization.AtPrime` is `Localization q.asIdeal.primeCompl`, and
   `IsRegularLocalRing` extends locality and Noetherianity with the equality
   of maximal-ideal generator rank and Krull dimension. These are precisely
   the two recorded dependency notions, without a new regularity predicate.
7. Conclusion: the full regular locus in Spec A is open. Lean:
   `IsOpen {q : PrimeSpectrum A |
   IsRegularLocalRing (Localization.AtPrime q.asIdeal)}`.
   Exact: every regular prime is included, and no assertion of nonemptiness,
   density, or regularity of all of A is added.

Edge cases: for the zero ring there are no prime ideals, the premise is
vacuous, and the empty regular locus is open. For a field the unique prime
quotient has the whole one-point regular open. The empty open is correctly
excluded by `U.Nonempty`; an empty regular locus of A is permitted by the
conclusion. A nonreduced ring such as k[epsilon]/(epsilon^2) is not excluded.
There is no dimension parameter in the signature, so dimension zero and the
empty regular sequence used in the proof remain permitted. No characteristic
is fixed. Quotients, spectra, and localizations use the arbitrary universe u;
there is no independently small test-object universe or hidden universe
identification. All variables and universes are explicitly bound.

Independent searches through `msearch.py`, using different terms from the
worker's primary search:

- LeanFinder: `Nagata criterion J-1 nonempty nonsingular open subset of each
  prime factor ring` returned eight integral-spectrum/Noetherian-related hits;
  none states this criterion.
- Loogle: `IsNoetherianRing, IsOpen, Localization.AtPrime` returned no hits.
- LeanSearch: `The singular locus is closed if the nonsingular locus of every
  prime factor ring contains a nonempty open subset` returned smooth and
  unramified loci and general Zariski closedness results. None is the theorem:
  the relative smooth locus requires a base algebra and different hypotheses.
- Grep wrapper: `isOpen.*[Rr]egular|[Rr]egular.*[Pp]rime[Qq]uotient|JOne|JZero`
  returned unrelated topological regularity, measure regularity, graded-ring
  projections and author names; no matching ring criterion.
- Direct `rg` of Mathlib RingTheory and AlgebraicGeometry, upstream
  `WeilConjectures`, and project `lean/Sheaf`, with `regular.?locus`,
  `singular locus`, and `intersection-regular-with-closed`, found no existing
  exact theorem. Project `JTwoResidueFieldCriterion` is different: its actual
  signature assumes finite models for purely inseparable residue extensions
  and concludes openness for finite type algebras. I opened that declaration;
  its proof step 6 uses this item, so it cannot replace it. `ExcellentRing`
  records the J-2 property rather than this implication. Exact-name checks
  in upstream, Mathlib, project Lean and `dag/lean_names_upstream.json`
  found no collision with the delivered declaration.

The module introduces no definitions, private copies, helper theorems, new
nodes, or dependency modules. Its sole theorem has precisely `by sorry`.
Both docstrings cite 07P9, 07P7 and this blueprint id. I matched all seven
proof steps against the node: generalization stability; parameters and their
numerators; spreading the regular sequence; finite denominator clearing and
localization exactness; a principal open in the quotient; quotient
localization and regularity lifting; Nagata's criterion and union of opens.
The module and declaration conform to the namespace and line-width rules.
No source-based statement correction or citer audit is needed.

Mismatch repaired: the proof-dependency node
`lem-exc-nagata-principal-open-criterion` now has an upstream attachment to
`Ideal.exists_notMem_forall_of_isNoetherianRing`. I read its signature in
`WeilConjectures/Mathlib/RingTheory/Spectrum/Prime/Noetherian.lean`: it takes
exactly generalization stability and the principal neighbourhood condition
in V(P), and supplies a principal neighbourhood in the entire spectrum.
I added `import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian`
without `public`, as the stage-2 proof-import convention requires. The two
other new algebra lemmas remain unstated proof dependencies and need no
module to express this item. Nothing else in the Lean or node was changed.
The previous worker's claim that the Nagata prerequisite had no recorded
module should be read with this updated attachment and import.

Second-reader validation: the repaired module passed `scompile.py Q34
lem-exc-regular-locus-open-from-prime-quotients
lean/Sheaf/RingTheory/RegularLocusOpenFromPrimeQuotients.lean`, with both
sandbox and library checks clean (12.7 s and 4.6 s respectively). I also
checked that `lean.statement` is verbatim the file's theorem signature and
that every Lean line is at most 100 characters. No unbound variables,
extra typeclass assumptions, errors or warnings remain.
