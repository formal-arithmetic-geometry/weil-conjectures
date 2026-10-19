## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-local-colimit-regular.json`: statement, split; eight proof steps, no Mathlib match. The statement and its three statement dependencies are unchanged.
- `citations.json`: fifteen step/node entries, each quoting the complete verbatim statement of the cited node.
- `searches.jsonl`: retained the interrupted attempt's searches and added a second semantic phrasing and a grep of RegularLocalRing. No unexecuted search was added.

New nodes: 0. New Mathlib leaves: 0. All supporting results already have DAG nodes, so there is no new statement-only lemma to deliver.

## Attachments

No attachment for the item. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for its blueprint tag, regular-local terminology and regular/colimit combinations found no declaration proving this directed-colimit assertion. The exact upstream master was also searched by the item's tag; it supplies no attachment. In particular the source declarations about smooth or etale stalks do not give the item for arbitrary local transition maps.

Existing attachments reused, not changed: `IsRegularLocalRing.isDomain` belongs to `lem-sc-regular-local-domain`; `IsRegularLocalRing.quotient_span_singleton` belongs to `lem-weil-pbc-regular-local-hypersurface-criterion`. Their recorded slopmaster2 audits are closed. The latter's stronger generator-count clause is not taken from its Lean: the proof uses only the quotient regularity actually in the DAG statement.

## WANTED

None. All sources used are present locally.

## What was wrong or missing

The item was an unsplit, statement-only child of `lem-per-smooth-colimit-regular`. Its statement agrees with Stacks 07DX (`algebra.tex`, `lemma-colimit-regular`), including nonempty directed indexing, local transition maps, regular local stages and a Noetherian colimit. No statement dispute or correction was necessary.

The source compresses the locality of the ring colimit and its canonical maps, domain formation without injective maps, the passage to the tail, and the quotient-colimit universal property. These are now written out. Its induction on cotangent-space dimension is expressed as strong induction on the least number of maximal-ideal generators. Nakayama, cited as an existing node, proves that a first member of a minimal generating set lies outside the square; after quotienting that generator the maximal ideal has strictly fewer generators. This avoids an uncited cotangent-dimension comparison while preserving the source argument.

The final appeal to 00NU is expanded: the existing 00KW dimension equality plus lifts of quotient maximal-ideal generators prove regularity. No new node merely restates 00NU or the item's conclusion.

The inherited blueprint ancestry identifies the regular strict-local reduction through the smooth-colimit lemma. The current main-20261015 ancestor markdown contains its statement without a proof; the inherited finer place, already recorded by the parent split, supplies this node's location. The chapter/unit records were read and left untouched. This is local commutative algebra inside that existing branch, with no change to a chapter or unit route and no SGA citation.

## Mathlib and duplicate searches

Read and retained the interrupted attempt's search log. It records grep, LeanSearch, Loogle and LeanFinder for this item's assertion; their hits concern direct-limit constructions, regular sequences, finite Krull dimension and local-ring criteria. The additional LeanFinder query was `Regular local rings are closed under directed direct limits when the limit ring is Noetherian`; it returns the finite-dimension instance, the DVR equivalences, Noetherian localization, and `Ring.DirectLimit.induction_on`, `exists_of`, the direct-limit type and its ring structures. None gives regularity of a Noetherian colimit. The additional grep `IsRegularLocalRing|IsRegularRing` in `RingTheory/RegularLocalRing` returns the definition and polynomial-ring results; their declarations were inspected. No matching theorem is present.

The item's earlier creator's Mathlib search records remain intact; newly appended records reproduce actual entries in this sandbox's log. The log records summaries of results, not replacement invented queries. No service-unavailable result has been represented as proof of absence.

Whole-DAG searches by `07DX`, regular-local/colimit terminology, `00NQ`, `00NU`, `lemma-regular-ring-CM`, `lemma-regular-mod-x`, Nakayama, and ring-colimit/cotangent filenames located the existing tools. Whole-blueprint searches were run for `regular local`, `Nakayama`, `quotient regular`, `Noetherian directed`, `07DX`, and `colimit`; no other blueprint node states this item. The item's `same_as` remains the searched empty list. The blueprint ancestor tool confirmed `lem-per-artin-gabber-affine-curve`.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. The existing hypersurface lemma supplies exactly the parameter quotient needed; the existing domain node supplies exactly the domain input. No copies of either were made.

## Review by N6

I read Stacks `algebra.tex`, Tag 07DX, statement and complete proof, and then the actual sources of the auxiliary steps: 00D6/00D7 for elementwise colimits, 00E9 for units in local rings, 00DV for Nakayama, 00NP for regular local domains, 00NQ for the parameter quotient, 00KW for the dimension equality, and 00NU for lifting regularity. I also read `categories.tex`, definition-colimit (002F), for the universal-property arguments. There are no new nodes needing a separate source review.

1. Step 1 uses `lem-pc-filtered-colimit-commrings-elementwise`. Its statement gives BOTH representation and equality after maps to one common object, for a small filtered category of commutative rings. A nonempty directed poset meets these hypotheses. Closure of the proposed ideal and its properness are proved by common-stage calculations; neither injectivity nor a module-colimit comparison is assumed.
2. Step 2 uses the same elementwise statement and `lem-weil-pbc-local-ring-unit-criterion`. The latter really states that an element outside the unique maximal ideal has a multiplicative inverse. This proves that every element outside the proposed proper ideal is invertible. The quotient is a nonzero field, every other proper ideal lies inside this one, and all coprojections contract it to the stage maximal ideal. Those conclusions are derived in the step, not imported from a definition node.
3. Step 3 uses `lem-sc-regular-local-domain`, whose statement explicitly gives nonzero and no zero divisors, and the elementwise-colimit node, whose equality clause makes a zero product zero at a later stage. The dichotomy is applied in that later domain. The proof never asserts that a structure map or transition map is injective.
4. Step 4 uses `def-weil-pbc-noetherian-ring` to make the maximal ideal finitely generated, `lem-weil-pbc-nakayama-local-generators` for the finite module equal to that ideal, and `def-weil-regular-scheme` for regularity in the field case. The Nakayama statement compares generators of M with generators of M/mM, so M=m gives exactly m/m^2. If the first minimal generator were in m^2, the others would span this quotient and would generate m, a contradiction. The induction is explicitly universal over all diagrams and strong, so an arbitrary smaller generator number in a quotient is covered.
5. Step 5 uses the elementwise statement to represent x, and the existing hypersurface criterion. I verified that this criterion assumes regular local R and f in m but outside m^2, and concludes quotient regularity. All of these hypotheses hold at EVERY index in the tail: the images of the stage maximal ideals lie in the limit maximal ideal, so a square-membership at any stage contradicts the choice of x in the limit. No flatness is needed.
6. Step 6 cites only `def-weil-pbc-category-colimit`, whose statement is the ring-cocone universal property being checked. It constructs the extension of a tail cocone, explains independence using a common upper bound, and then factors a map killing x through the ring quotient. These are direct universal-property calculations, not an invocation of an unrecorded cofinality or quotient-preservation theorem. The tail is small, directed and nonempty.
7. Step 7 cites the unit criterion and the Noetherian definition. It derives quotient locality, verifies contraction of maximal ideals for the quotient transition maps using the ORIGINAL locality hypotheses, and proves quotient Noetherianity by taking inverse images of ideals and then images of finite generating sets. The quotient maximal ideal is generated by the last n-1 original generators. Hence every hypothesis of the strong induction is checked before it is used, and its parameter strictly decreases. Regularity of the quotient stages was already proved in step 5.
8. Step 8 uses `lem-weil-pbc-dimension-quotient-nonzerodivisor`, which states the exact equality dim(L/xL)+1=dim L for a Noetherian local ring and a nonzerodivisor in its maximal ideal. The nonzerodivisor hypothesis follows from step 3 and x nonzero; the other hypotheses were retained from the item or established in step 2. The definition of regular local ring supplies the quotient generators. The displayed lifting calculation proves that x together with their lifts generates the original maximal ideal, with exactly the required dimension count. No additional 00NU node is needed because this lifting argument is written in the step.

I checked B--E of delivery-errors against these files. There are no new definitions, no unnamed non-elementary inputs, no new lemma standing in for an item clause, and no use of a cited node's proof in place of its statement. Each step citation is present in citations.json as a verbatim quotation. Every non-elementary assertion outside the induction is one of the cited node statements. The elementary colimit arguments are written out, and every proof step is shorter than 2000 characters.

Small cases: a constant field gives n=0 and dimension zero; a constant DVR with its uniformizer gives the n=1 reduction to its residue field; Z_(p) with x=p checks the mixed-characteristic case. The noninjective local map k[t]_(t) -> k, followed by a constant tail, has colimit k and is correctly handled by the n=0 case. It also illustrates why no injectivity hypothesis is permissible. A zero colimit is excluded by the proof of properness of m, using the local, nonzero stages and eventual equality. Empty indexing is explicitly excluded in the statement. The proof does not use a Noetherian or uniform-dimension bound on the whole diagram beyond the given regularity of each stage and Noetherianity of the colimit.

The repairs made during self-review were to spell out the strong induction hypothesis, prove the strict decrease using minimal generators and Nakayama, expand the tail and quotient universal properties, and replace a potential uncited appeal to the regularity-lifting theorem by its dimension-and-generators argument. No statement was changed. The off-unit citations are generic algebra tools, listed in split_report.tool_uses; they replace no unit step.

## Unfinished work

None in the split. Server dry-run validation and direct delivery follow this report.
