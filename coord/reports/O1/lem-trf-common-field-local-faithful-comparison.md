## Worker report

Item: lem-trf-common-field-local-faithful-comparison. Group: O1. Stage 1 only.

Files written: dag/nodes/sec-trace-formula/lem-trf-common-field-local-faithful-comparison.json (statement, split; not an exact Mathlib leaf), citations.json (nine step/node quotes), report.md, and the search command's searches.jsonl. No new nodes or Mathlib leaves were created. The original statement, its four statement dependencies, source, creation record, and blueprint ancestry are retained.

Attachments: none for this item. The project-wide tag and concept searches found no declaration proving the whole comparison. Field.exists_common_extension in WeilConjectures/FieldTheory/CommonExtensionFields.lean:40 proves the existing common-extension node, not this item's prime lifting and local-ring comparison; its source and proof were read. This delivery cites that existing DAG node and does not claim the whole item as an attachment.

WANTED: none.

The item had an empty proof. No statement correction or source error was necessary. The six steps follow the common-extension/local-ring passage in Stacks Varieties Tag 0384 (lemma-geometrically-reduced-upstairs), using Fields Tag 0H7K (lemma-common-extension-field), Algebra Tag 00HQ (lemma-ff-rings), Tag 00HT (lemma-flat-localization), and Tag 00HR (lemma-local-flat-ff). The original source application has a finite purely inseparable extension on one side; the algebraic comparison isolated in this item's statement works for arbitrary extensions because only faithful flatness and prime contraction are used. We do not claim that one can prescribe arbitrary primes on BOTH tensor factors simultaneously: only the prime on the L side is prescribed.

The current chapter and sk-i-curve-zero unit were read. This remains an algebraic tool on the inherited Curves 0C4D/geometric-reducedness branch recorded in blueprint.from.place. It changes no chapter or unit route. The single off-unit non-Mathlib result, lem-weil-common-extension-fields, is declared in split_report.tool_uses as a field-theory tool. No unit realization file is needed because the item is not the unit's key statement.

Searches: ran the required command for LeanFinder, Loogle, grep and LeanSearch, plus a second LeanFinder formulation; all five returned and were read. The log and item record preserve the exact queries and results. Existing imported search records are retained. Hits include Ideal.exists_isPrime_liesOver_of_faithfullyFlat, RingHom.Flat.localRingHom, instFlatAtPrime and PrimeSpectrum.comap_surjective_of_faithfullyFlat. Their source was read in Mathlib/RingTheory/Flat/FaithfullyFlat/Algebra.lean:60,138,146 and RingTheory/RingHom/Flat.lean:108. These are components, not an exact full-item result. The linear-disjointness hit additionally assumes a domain tensor product, which is not a hypothesis here. No Lean or compiler was run.

The DAG was searched by common-extension words and by Tags 0H7K, 0384, 00HQ, 00HT, and faithfully-flat/localization concepts. The whole-blueprint searches for common extension, common field and faithfully flat were read. No blueprint node states the item. The existing algebra tensor pushout, scalar-extension faithful flatness, prime-spectrum surjectivity, flat local-ring map, and flat-local faithful-flatness nodes suffice. No newly named result duplicates an existing node; there are no new-node same-tag pairs to compare.

## New nodes

None. The elementary tensor identification and contraction calculation remain steps rather than separate nodes.

## Not duplicates

No new nodes.

## Review by O1

I read the actual source paragraphs in varieties.tex, lemma-geometrically-reduced-upstairs (0384), fields.tex, lemma-common-extension-field (0H7K), and algebra.tex, lemma-ff-rings (00HQ), lemma-flat-localization (00HT), and lemma-local-flat-ff (00HR). I checked the statement of every cited node, rather than relying on its title or proof. The item introduces its own rings, embeddings and primes; its notions are supplied by the four existing definition nodes. There is no new node with missing hypotheses, undeclared objects or an unverified Mathlib match.

Step 1 uses lem-weil-common-extension-fields, whose statement gives a common field for arbitrary extensions, not just finite or algebraic ones. Its embeddings are k-field embeddings, exactly what is needed for both scalar structures to restrict to the same k-structure. Although the Fields proof omits the general Zorn argument, this delivery uses the existing theorem's full statement rather than reproducing or silently invoking that omitted argument.

Step 2 uses the actual construction and universal property clauses (1)--(3) of lem-weil-pbc-algebra-tensor-pushout-universal-property and the pure-tensor generation clause of def-weil-pbc-module-tensor-product. I wrote both directions of the identification (R tensor_k H) tensor_H F = R tensor_k F, checked balancing and multiplicativity, and computed both composites on generators. Thus this is an elementary two-way map calculation, not a hidden uncited associativity theorem or a new clause-node restating the item. The same calculation with H=E and H=L gives precisely the two maps in the statement.

Step 3 uses lem-weil-pbc-field-extension-base-change-faithfully-flat with K=H, K'=F, D=R tensor_k H. The hypothesis is satisfied because each i_H is a field embedding; R_H is a commutative H-algebra. Its statement asserts faithful flatness for arbitrary commutative D with no Noetherian or finite-generation assumption. I checked invariance under the explicit ring identification by its linearity and the exactness definition in def-weil-pbc-faithfully-flat-ring-map; that definition also explicitly supplies flatness. This spells out what would otherwise be hidden in the word 'transport'.

Step 4 uses lem-weil-pbc-faithfully-flat-surjective-spectrum, whose statement supplies a prime over EVERY prescribed prime. It is applied to S to T after Step 3, not to a merely flat map. I checked primality of P by the product test and properness, and wrote the membership equivalence proving its contraction is p. The two composites from R agree because both send r to r tensor 1; no joint-prime existence over two independently chosen primes is assumed.

Step 5 uses lem-weil-pbc-flat-local-ring-maps. Its statement gives the displayed fraction formula, flatness and locality for any prime over its contraction. Those hypotheses hold for Q and P by Step 4 and flatness by Step 3. I do not use its conditional Noetherian conclusion. The maximal ideal description is the statement of def-weil-pbc-localization-at-prime. I checked denominator validity and the equivalence t in P iff j_E(t) in Q, which yields the exact inverse-image equality of maximal ideals demanded here, not just a vague use of 'local'.

Step 6 uses lem-weil-pbc-flat-local-hom-faithfully-flat, which explicitly says that a flat local homomorphism of local rings is faithfully flat. Both rings are local by the localization node, flatness and the local condition were established in Step 5. Its extra spectrum-surjectivity clause is not needed here. All nine step/node uses have a quote copied verbatim from the cited statement in citations.json; each quote was checked against the source JSON.

For the small cases, E=k or L=k simply makes one embedding the base embedding; E=L and the identity case cause no change in the calculations. Transcendental and infinite algebraic extensions are covered by the arbitrary-extension node and the scalar-extension leaf. If R=0, then S=0 has no prime q, so the hypotheses cannot be met; no invalid choice of Q is required. Nonreduced rings such as k[epsilon]/(epsilon^2) are allowed, and a prescribed prime need not be maximal. The proof never assumes a domain tensor product, separability, finite degree, Noetherianity, or finite generation. In particular tensor products of inseparable fields may be nonreduced, which affects none of the arguments.

I checked delivery-errors B through E against the written files: statements and hypotheses are unchanged, no spurious elementary or duplicate node was introduced, every non-elementary step has a theorem citation giving exactly its claim, the proof is not moved wholesale into a new node, and no circular dependency is added. All six steps are below 2000 characters; the longest is the explicit elementary tensor calculation. I corrected the potential implicit tensor-associativity and local-map-identification gaps by writing the formulas and membership equivalences. There is no unfinished mathematical part.

Validation: the required deliver.py --no-push exited successfully with OK at 94944ae5682 (server preflight passed). The first run only rejected the short Step 6 quote; replacing it with the full verbatim node statement resolved that diagnostic. No mathematical or node-file change was needed. The subsequent push uses the same verified node and citations, with this report recording the result.
