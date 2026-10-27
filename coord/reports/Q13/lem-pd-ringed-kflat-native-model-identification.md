# Worker report: lem-pd-ringed-kflat-native-model-identification

## Files written

- dag/nodes/sec-poincare-duality/lem-pd-ringed-kflat-native-model-identification.json — statement retained verbatim; seven proof steps; status split; no Mathlib match.
- citations.json — 18 citations with verbatim extracts from the statements actually used.
- searches.jsonl — five new searches executed by the required msearch.py command; the item's five inherited search records were retained.
- report.md — this report and the direct-delivery self-review.

There are zero new nodes and zero new Mathlib leaves. Every non-elementary fact used is already a DAG statement. All seven steps are under 1,000 characters, so none hides a claim behind an over-2,000-character step.

## Attachments

None. Searched lean/WeilConjectures for the exact item tag and ringed/native K-flat comparison terms. The existing derived monoidal equivalence and unit files concern the native abstract construction, not an identification with the independently constructed ringed-site tensor and its specified arbitrary-pair transformation. They do not state the whole item. No Lean was written or compiled.

## WANTED

None. The source texts needed here are present in literature/.

## Corrections and scope

No statement dispute and no change to the item statement or its statement dependencies. The original item was statement-only, not a prior completed split. No pre-existing Q13 attempt or search log was present. I retained its existing source, creation stamp, blueprint chain and Mathlib records, and supplied the proof, tool-use declarations and additional executed searches.

The current blueprint is literature/blueprint/latest/ at ef6f9619fdbffa59e88528fb56483d76c70258c8. I read its Poincare-duality chapter text, the Verdier-exchange unit and the abstract derived-monoidal statement and proof. The DAG's unit record reflects an older formulation of Verdier exchange; this item is a generic technical comparison on the seeded target's existing route, so neither the unit nor the chapter is changed. The nearest blueprint ancestor command returns None, as in the existing item's blueprint.from.node. Its precise seeded-target place and via chain are preserved. Searches for “native model identification”, “ringed native tensor” and “K-flat derived tensor” found no blueprint node stating this comparison. The latter returned projection-formula results, not this identification.

## Mathlib searches and results

All additional searches were made through /home/ubuntu/weil-launcher-all/batch2/msearch.py Q13 lem-pd-ringed-kflat-native-model-identification. Their exact queries and raw result records appear in the item and searches.jsonl. I used LeanFinder twice, changing the question to uniqueness of total left-derived bifunctors, LeanSearch once, Loogle once, and the required Mathlib grep once.

The first semantic search found ordinary flatness, projective Tor and presheaf derivations. LeanSearch found Module.Flat exactness criteria and HomologicalComplex.Acyclic. The second LeanFinder search found CategoryTheory.Functor.leftDerivedUnique and its compatibility lemmas. Loogle and grep found CategoryTheory.Localization.Monoidal.tensorBifunctorIso (Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean:135). I read that file's tensor-stability assumptions (IsMonoidal:43ff) and declaration (135ff), the LeftDerived uniqueness interface, and Tor.lean:40ff. These are relevant generic APIs, but none states the equivalence of the two K-flat tests on ringed sites together with the identification of both given models, arbitrary-pair localization maps, and all constraints. In particular ordinary monoidal localization requires tensor-stability of the arrow class; quasi-isomorphisms of all complexes do not meet that hypothesis. No unavailable search was reported as absence.

## Not duplicates

No new node was created. Reuse searches included the full DAG's K-flat/native tensor titles and statements, the Stacks tags 06YP, 06YS, 06YT, 06YU, 0FPQ, 0FPT and 07A2, and the blueprint searches above. The already existing ringed-site descent theorem supplies the comparison extension, and the native flat-term tensor theorem supplies closure. The scheme-only bifunctor descent node and the one-point-ring quasi-isomorphism node were inspected and deliberately not used for arbitrary ringed sites.

## Review by Q13

I performed this self-review with the item, the cited statements and the source texts open, under the direct-delivery brief. It is not a claim of an independent second worker's review.

For the item I read Stacks sites-cohomology.tex, lemma-K-flat-quasi-isomorphism (06YP), lemma-K-flat-resolution (06YS), lemma-derived-tor-quasi-isomorphism-other-side (06YT), the construction and definition-derived-tor (06YU), lemma-tensor-product-K-flat (07A2), lemma-symmetric-monoidal-cat-complexes (0FPQ) and lemma-symmetric-monoidal-derived (0FPT). I verified the tag/label mapping in tags/tags. The last two proofs are omitted in Stacks: the independent-model comparison and explicit coherence checks are therefore honestly marked proof_origin.by = agent. I also read injectives.tex remark-existence-D (079Q), whose last sentence includes module sheaves on a ringed site among Grothendieck categories. There are no new nodes whose sources need separate approval.

Step 1 uses exactly the assertion of lem-weil-pbc-total-tensor-homotopy-cone-signs that acyclic-test K-flat complexes preserve every quasi-isomorphism on both sides, with arbitrary endpoints. def-pc-kflat-complex and def-sfb-preserves-kflat-quasi-iso give the two definitions and identical signed total tensors. The reverse implication is written out using the quasi-isomorphism from the zero complex to an acyclic complex. Thus a theorem, rather than just the definition of flatness, supports preservation of quasi-isomorphisms. Flat terms are never used here.

Step 2 uses lem-weil-pbc-site-derived-tensor-descent, whose statement explicitly gives extension and uniqueness of any natural transformation on the flat-term resolving subcategory, for arbitrary target bifunctors. Its restriction is precisely the category P in the item, not an arbitrary category of site presentations. lem-sfb-derived-monoidal supplies the abstract model's K-flat computation. The proof constructs e = rR composed with inverse ra and its inverse; applying the descent statement to both and using uniqueness proves invertibility. It does not invoke an unnamed comparison theorem or move the item into a fresh node.

Step 3 uses lem-pc-kflat-resolution, which explicitly provides flat terms, K-flatness and a quasi-isomorphism for every unbounded complex on any ringed site. I checked all three properties, not just existence of some resolution. The rest is the displayed naturality calculation with the two model maps already specified in the item. Only the derived bifunctor images D_a and D_R are cancelled. The ordinary tensor of two augmentation maps is not assumed invertible. Marking this cancellation step elementary does not replace a lemma: its only non-elementary input is the cited resolution theorem.

Step 4 uses the signed tensor lemma with arbitrary endpoints, separately for each of the four arrows in the two displayed factorizations, and def-pc-tensor-complex-sheaves for bifunctoriality. The K-flat factor is Q then U in the first factorization, and P then V in the second. This proves the one-K-flat claim without presuming flat terms. Inverting the already proved transformation equation identifies the canonical model maps on every K-flat pair.

Step 5 checks the hypotheses of lem-pur-flat-term-kflat-tensor-native before applying it. The coefficient category is Grothendieck by lem-weil-pbc-ring-sheaves-grothendieck, closed and symmetric by the item's stipulated sheaf tensor, and both inputs are categorically K-flat by Step 1. Their terms are flat by membership in P; symmetry identifies the one-sided sheaf flatness definition with the categorical two-sided version. The cited theorem explicitly concludes both K-flatness and flatness of all total-tensor terms. The regular degree-zero unit has flat terms (R and zero), and preserves acyclicity because tensor with it is identity. Thus each intermediate pair in Step 6 really lies in P. The argument uses smallness relative to the coefficient universe, never equality of the original object, morphism and coefficient universes.

Step 6 reads only the constraint clauses of lem-sf-ringed-derived-closed-symmetric-monoidal and lem-sfb-derived-monoidal: both statements say that associators and unitors are induced from the complex constraints. The common signed total complexes are fixed in the item. I wrote both left- and right-associated model identifications C_L and C_R, the two naturality equations for w, and the resulting associator equation. Its domain and codomain are respectively B_a(B_a(X,Y),Z) and B_R(X,B_R(Y,Z)); all composites have those types. Site-derived-tensor descent states that the resolving localization is an equivalence, so every derived object is isomorphic to a resolving one. Naturality therefore carries the equation to all derived triples; this does not require a new unsupported three-variable existence claim.

Step 7 uses the same two constraint clauses, now at the regular degree-zero unit, and the same site-descent equivalence. The two unitor equations follow by cancelling their respective model isomorphisms. With the identity unit comparison they are exactly the unit conditions. The final claim follows by composing a given comparison with w inverse and substituting the already proved equations, not by silently transporting a different comparison map.

I checked the small cases: the zero complex, zero ring, empty site, the unit R[0], genuinely unbounded inputs, and K-flat complexes whose terms are not flat. For the last case the contractible complex with identity differential on Z/2 in two consecutive degrees is K-flat despite nonflat terms, and Steps 1 and 4 still apply. Conversely Z/2[0] is not K-flat over Z: tensor the acyclic complex Z --2--> Z --> Z/2 with it to obtain nonzero cohomology in the lowest degree. For two inputs Z/2[0], the derived tensor has a nonzero Tor term whereas the ordinary tensor does not, so Step 3 must not invert T; the written proof does not. With Z[0] in one slot, Step 4 correctly makes the transformation invertible with arbitrary other input. These checks catch the main possible accidental strengthening.

For delivery-errors B–E I checked that the statement is self-contained with its existing definition dependencies; no statement-only node contains a hidden proof because no new node exists; every cited mathematical assertion is in its cited statement; citations.json quotes those statements, not their proofs; every non-elementary input has a node; no conclusion is restated as a new dependency; and no forward use of the comparison is needed to construct it. Formula text uses single-escaped TeX. The displayed augmentation calculation and associator equations replace potentially ambiguous “transports” language. I added generic tool-use reasons for all off-unit theorem citations. No SGA source is used.

## Unfinished work

No mathematical part remains. The required dry run and push are the remaining delivery actions.
