## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-string-central-parity.json`: item split into six steps; statement, statement dependencies, inherited source, creation metadata and previous searches retained. One new proof dependency.
- `dag/nodes/sec-six-functors-basics/lem-sfb-rank-two-root-coordinate-classification.json`: statement-only lemma; unsplit, no Mathlib match. States the four possible complete coordinate lists of a rational reduced crystallographic root plane, without any Lie brackets or parity assertion.
- `citations.json`: exact quotations for the node used in steps 2 and 4. `searches.jsonl` records the actual searches. Coordinate-check scripts and the extracted local source text remain scratch material.

## Attachments

None. Searched the live project under `lean/WeilConjectures/` for the item id, Chevalley, root-string and rank-two terminology. There is no declaration stating this item or the new classification. Occurrences of Chevalley concern constructibility and valuation extensions, rather than Chevalley bases. No compiler or build tool was used.

## WANTED

None for this split: the needed rank-two classification and assumed bracket constants are in the obtained Milne book. The earlier ancestors' wanted integral-enveloping-algebra sources are not used here.

## Findings and changes

The imported item is true as stated; no STATEMENT-DISPUTED or statement correction is needed. The empty proof lacked the rank-two calculation, including the signs in the grouped half-sums. The proof now chooses the root of smaller explicit coordinate norm first and checks complete root sets, rather than presuming the given pair is a simple-root pair. The unequal-length orientation matters. The two exceptional strings are G2 with (p,q)=(0,3) and (1,2); their respective half-sum numerators have magnitudes (1,3) and 6. This establishes integrality for arbitrary Chevalley signs without an unproved sign convention.

The chapter and unit were read. The item's inherited chapter is sec-six-functors-basics whereas its unit record sk-thm-sf-ctf-stability is filed with chapter sec-six-functors. The latest blueprint text for the stability unit was also read; it has no rank-two root-system node. This item is a supporting lemma far below the existing alteration/moduli/Chevalley chain, whose route is retained. `blueprint_refs.py ancestor` returns None because the inherited creation chain has no resolved blueprint ancestor; the item and new node retain null for from.node and carry the full inherited supporting place and via chain. No unit or chapter is changed.

The Mathlib searches were made with msearch.py, including a second semantic phrasing for both questions. The actual results are recorded with the exact queries. Read the candidate sources: Chain.lean:475 bounds root strings, GeckConstruction/Basic.lean:351 gives one bracket in Geck's particular model, Finite/G2.lean:308--316 lists an already supplied embedded G2, and Finite/Lemmas.lean:104--122 bounds Cartan-integer pairs. The G2 list requires an EmbeddedG2 hypothesis and does not supply the four-way classification for arbitrary rank-two systems. None proves this item, nor is the classification a one-line specialization. The new node remains unsplit, with no proof or proof dependencies.

## Unfinished work

The one new classification lemma is intentionally statement-only, for the next stage-1 item. The current item's argument is complete. No Lean was written, compiled or built. No repository or launcher file was changed.

## Review by Q26

I read Milne, Algebraic Groups, Appendix C.12 and C.14 on printed p.610 for the reflection/integrality axioms, C.17--C.18 on p.611 for rational scalar extension and reducedness, and section g, table (180) and all four diagrams on pp.621--622 for the new classification statement. The four displayed lists in the new node reproduce those diagrams with the short simple root named s in B2 and G2. This is a standalone classification of root sets, not a restatement of the item's centrality or parity clauses. I also read Section 23h, Theorem 23.71, pp.508--509; its magnitude formula is already a hypothesis of the item, so the split does not assume the existence or normalization theorem again. The proof is explicitly marked agent-written: Milne does not state the half-sum consequence.

For step 1, reducedness excludes dependence for the given distinct nonopposite roots. Restricting reflections and coroot functionals preserves all the new lemma's hypotheses: the root set is finite, spans the two-dimensional plane because it contains the original pair, and has integral pairings and no extra multiples. No structural theorem is used in this restriction argument.

Step 2 cites the new node's actual conclusion giving a rational basis and one of four complete root sets. I opened the written statement and checked that it gives equality of the whole root set, not merely containment or a list of some roots. That equality is precisely what permits membership and absence tests. I checked the norm polynomials against the four lists, then enumerated every ordered independent pair for which L(a) <= L(b), including both orders at equal lengths. The possible (p,q) rows in the proof are exhaustive. The independent coordinate calculation checked 8 pairs in A1 x A1, 24 in A2, 32 in B2 and 84 in G2: all strings are contiguous, and p+q <= 3. This is finite integer arithmetic on the cited coordinate lists, not an appeal to an uncited Weyl-orbit theorem.

For step 3, I checked the endpoint and the shifted bottom coefficient p_{a,b+ka}=p+k. Multiplying the k successive assumed bracket constants and dividing by k! gives exactly a signed binomial coefficient; the formula includes k=0. The next root is absent and cannot be zero by independence, which justifies every higher vanishing. No divided-power assertion in an enveloping algebra is used.

Step 4 again cites the new node's full coordinate-list conclusion, and citations.json quotes it verbatim. I checked all i<j, not just adjacent pairs. The only root sums are the two pairs of total index 3 in the G2 (0,3) string and the pair (0,1) in the G2 (1,2) string. The bottom coefficients are respectively 0, 2 and 2. The same coordinate comparison excludes each further root of coefficient 3 in b, so the centrality argument has the required root-absence information. I checked the table and these exclusions for all 148 oriented pairs with audit_coordinates.py; all assertions pass.

For step 5, bilinearity and the zero-bracket hypothesis apply to actual root vectors of the displayed weights; all candidate sums are nonzero because a,b are independent. Alternation handles repeated indices and skew symmetry handles reversed ones. Thus no opposite-root Cartan term was missed. For step 6, the signed numerator (plus or minus 1 plus or minus 3) is always even, and the other numerator is plus or minus 6. I checked q=0, empty sums, weights outside R, and roots with a zero grouped sum; zero coefficients supply the required integer in the last case. Independent sign choices already suffice, so no unproved compatibility of Chevalley signs is needed.

I checked delivery-errors B--E against these files: the new node is self-contained and statement-only; each non-elementary input is a cited node; the quotes are literal substrings; the new node has no dependency back on this item, so there is no new cycle; no small arithmetic fact or clause of the item was extracted as a node. The only new lemma is the non-elementary root classification. Every non-elementary step is shorter than 2000 characters. Existing item fields and previous searches were retained, and the new searches reflect actual successful tool calls. The server check_dag check passed before the full delivery check.

## Not duplicates

- lem-sfb-rank-two-root-coordinate-classification vs lem-sfb-chevalley-string-central-parity: the new node classifies rational root sets; the item concerns brackets and integral half-sums of root vectors in a Lie algebra.
- lem-sfb-rank-two-root-coordinate-classification vs lem-sfb-chevalley-root-normalization: normalization supplies a Chevalley basis and bracket magnitudes, not a complete coordinate classification of a root plane.
- lem-sfb-rank-two-root-coordinate-classification vs lem-sfb-root-string-integer-interval: the existing Mathlib leaf states contiguity of one string; it does not enumerate every root in a rank-two system.
- lem-sfb-rank-two-root-coordinate-classification vs lem-sfb-serre-rational-presentation: the existing statement constructs a semisimple Lie algebra from Serre generators and relations; it does not state the four complete rank-two root sets.
- lem-sfb-rank-two-root-coordinate-classification vs lem-sfb-root-datum-lattice-embedding: the existing statement constructs the rational root-system/central lattice decomposition and weight lattice; it does not classify rank-two root systems.

Whole-DAG statement/title searches and blueprint_refs searches for root string, root system, rank two, rank-two, crystallographic and Chevalley found no blueprint node giving either this item or the new classification. No Stacks tag is appropriate for this Lie-theoretic classification, and no SGA source is used.

## Delivery-check repair

The first full dry run rejected the grouped definition reference in the new statement. I expanded it into two individual bracketed node references, matching its unchanged stmt_deps. Both literal conclusion quotations remain unchanged and were checked again. No mathematics or hypotheses changed.
