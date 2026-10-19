# Worker report

1. Files written: item `lem-weil-pbc-affine-closed-specialization-localization` (split, statement unchanged); new `lem-weil-pbc-localization-spectrum-embedding` (statement, Mathlib leaf); new `lem-weil-pbc-localization-ring-weakly-etale` (statement only, not in Mathlib, closed project attachment).
2. Attachments: `Algebra.WeaklyEtale.of_isLocalization` belongs to `lem-weil-pbc-localization-ring-weakly-etale`, WeilConjectures/Mathlib/RingTheory/Etale/Weakly.lean:46. Its statement is exactly the ring assertion. The committed map local/sorry_map_slopmaster2_7d675a26.jsonl.gz records s=false, ts=false and no project dependencies. The source proof is lines 46–53, without sorry; it uses localization flatness and bijectivity of tensor multiplication from Mathlib. I leave closure classification to lean_status.py. No Lean was written or compiled.
3. WANTED: none.
4. The imported item was true but had no proof. Its prior Mathlib-search records already mention useful ingredients but do not supply the quotient-unit argument. The project generalization declarations use units in (A/I)_f, and do not directly state the whole item with its displayed S and scheme weak etaleness; hence no full-item attachment is claimed. No statement dispute, changed hypotheses, or unit-route departure.
5. Nothing mathematical remains unfinished in the item. The two new inputs have a Mathlib match and a closed project declaration respectively. The second reader must verify and deliver.

## Searches and sources

Read proetale.tex Tag 096V (lemma-localization), lines 493–541, including both directions of the image proof. Read more-algebra.tex Tag 092B (definition-weakly-etale), lines 30189–30204 and its explicit following localization assertion. Read algebra.tex Tag 00E3 (lemma-spec-localization), lines 3163–3203; Mathlib RingTheory/Spectrum/Prime/Topology.lean:345–377 verifies embedding and range independently. Read algebra.tex Tag 00E0 (lemma-Zariski-topology), proof of (8), and Mathlib RingTheory/Ideal/Maximal.lean:80. All tags checked in tags/tags. Also read the item's chapter and unit, GOAL.md and dag-sync.md; this is an auxiliary affine tool below the qbar route, not the unit's key statement, so no unit record changes.

Searched the whole DAG by localization, weakly etale, proper ideal, maximal, Stacks tags 00E3/092B/092J/096V, and the exact project declaration. Blueprint searches included localization, multiplicative subset, proper ideal, maximal, weakly etale, localization is, primes disjoint, 00E3 and 092B. No blueprint states either new generic tool. Reused proper-ideal-contained-in-maximal and the basic-open basis node; the existing primes-of-localization node treats only prime-complement and single-element localizations, and the residue-field node gives a set bijection but not the topology. Existing retained-localization concerns a different ring with pairs of primes and a w-local statement, not this ordinary localization.

Every recorded new-node search was run through msearch.py. LeanSearch returned HTTP Internal Server Error and is recorded unavailable. LeanFinder and Loogle ran; I inspected the returned declaration types and the local Mathlib source. A second semantic phrasing for weak etaleness found localization flatness, which is only one of the two flatness conditions. The weak-etale declaration is in WeilConjectures, not Mathlib. The item-specific second phrasing again found generic prime-correspondence results, not the full assertion.

## Review by NE

I checked the item against the actual proof of 096V, with f=1. Its S is exactly the inverse image of quotient units; I is arbitrary. Step 1 proves multiplicative closure directly, takes both ring flatness conditions from the new weak-etale input, and uses the explicit ring/scheme equivalence in the statement of def-weil-pbc-ind-etale-algebra; this definition really states that equivalence. The generic localization assertion is not a node relabelling this item's special S or image. Its proof is already the closed project theorem, and no new proof sketch is hidden in its statement.

Step 2 uses precisely the embedding and disjoint-prime range clauses of the new spectrum input. Neither the existing prime-bijection statement nor the definition of Spec alone was used as a substitute for a topological theorem. Step 3 checks disjointness by lifting a quotient inverse and subtracting st-1; it is elementary and needs no cited lemma. Step 4 proves p+I proper before using the existing maximal-existence leaf. That node really gives a maximal ideal containing an arbitrary proper ideal, with no Noetherian hypothesis. I wrote out why this maximal ideal is prime, rather than silently invoking another theorem. The two inclusions now identify the embedding's range with the claimed set.

Step 5 uses only clause (i) of the existing basic-open node, which holds for every commutative ring. It proves the specialization explicitly in B: the denominator is a unit, and inclusion of contracted primes puts x in every basic neighbourhood of y. It does not use surjectivity or specialization-lifting for an arbitrary continuous map. All step citations have their actual statement copied in citations.json; I checked the quotes against the portions used.

Small cases: I=A gives S=A containing zero, B=0 and empty spectra, so every conclusion is vacuous and the image formula is empty. I=0 gives S=A^× and B≅A, so the image is all of Spec A and the specialization can be equality. The zero ring has the same empty-spectrum behavior. Non-finitely-generated ideals require no change: inverses modulo I use individual elements and the proper-ideal argument never chooses generators. General localization embedding permits zero in M. No extra nontriviality, finite presentation, Noetherianity or quasi-compactness hypothesis was introduced. I checked B1–B9, C1–C8, D1–D5 and E1–E7: new statements introduce all objects and fraction equivalence inline, carry no proofs, and use genuine general tools; no cycle or use of another node's proof occurs. The only correction during preparation was to reuse the existing maximal-existence node after the declaration search found it, instead of creating a duplicate. No source error was found.

## Not duplicates
lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-localize-localization-at-prime: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns Local rings of prime and principal localizations and does not state this general topological embedding.

lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-localized-finite-quotient-charts: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns Canonical local charts of a positive finite-algebra quotient and does not state this general topological embedding.

lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-localization-prime-residue-field-iso: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns Residue fields of a localization agree with those of the base and does not state this general topological embedding.

lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-polynomial-complete-local-fibre-reduction: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns Reduction of polynomial completion fibres to complete local domains and does not state this general topological embedding.

lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-localization-dimension-chains-below-prime: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns The dimension of the localization at a prime is the length of the longest chain of primes below it and does not state this general topological embedding.

lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-regular-through-localization: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns A regular map factoring through a localization is regular from the localization and does not state this general topological embedding.

lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-localization-of-regular-ring: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns A localization of a regular ring is regular and does not state this general topological embedding.

lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-fibre-ring-primes-bijection: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns Primes of the fibre ring are the primes over p and does not state this general topological embedding.

lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-primes-of-localization: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns Primes of prime and principal localizations and does not state this general topological embedding.

lem-weil-pbc-localization-spectrum-embedding vs lem-weil-pbc-localization-quotient-by-prime: new node states topological embedding and image for an arbitrary multiplicative localization; existing node concerns Primes of a localization and the quotients by them and does not state this general topological embedding.

lem-weil-pbc-localization-ring-weakly-etale vs lem-weil-pbc-affine-closed-specialization-localization: new node states only weak etaleness for arbitrary ring localizations, with a closed project declaration; existing node concerns Affine localization near an arbitrary closed subset, not this generic theorem.


## Dry run

The first captured preflight required an explicit mathlib_match.line field for the spectrum leaf, despite the verified lines already being in how. Added line 374 (embedding); range remains separately identified at line 353 in how. No mathematical change.

## Second reading by NE

I reread the item statement against Stacks tags 096V and 092B: the quotient-unit multiplicative set, specialization image, weak-etale conclusion, and absence of finiteness hypotheses all agree clause by clause; edge cases I=0, I=A, and the zero ring behave as stated.

Step 1 was checked against the weak-etale localization node and ind-etale definition; multiplicative closure is elementary and the cited ring/scheme equivalence supplies exactly the conclusion.

Step 2 was checked against the spectrum-embedding node and Tag 00E3; it uses only the stated embedding and disjointness image.

Step 3 was checked directly from the quotient inverse relation; the contradiction in a prime containing I is elementary and complete.

Step 4 was checked against the maximal-containment node; properness of p+I and the maximal-ideal-to-prime argument are written explicitly, with no hidden Noetherian assumption.

Step 5 was checked against the basic-open localization node; the denominator-unit reduction and specialization argument are elementary and establish the final clause.

The spectrum node was checked as a statement-only Mathlib leaf against Mathlib/RingTheory/Spectrum/Prime/Topology.lean lines 353 and 374; its hypotheses and arbitrary-submonoid range are self-contained. The weak-etale localization node was checked against the closed, sorry-free declaration Algebra.WeaklyEtale.of_isLocalization (Weakly.lean lines 46–53), with its statement matching the project theorem and no proof embedded. Searches and citations were verified against searches.jsonl and citations.json. No mathematical changes were required; only the explicit Mathlib line field was retained for preflight.

Second-reader changes: removed split_report.tool_uses because C8 reserves that field to the maintainer; the basic-open input is already a Mathlib leaf and requires no route exception. Ran independent Loogle and grep searches with fresh phrasings, recorded their actual results, and retained both new nodes: one supplies the general topological embedding, the other attaches the already closed ring-localization theorem. The similarly named smooth-purity node concerns localization of sites, not rings, and is not a duplicate. Rechecked every citation quote verbatim against the node statement.
