## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-fixed-pair-postnikov-identifications.json`: item, statement unchanged, seven proof steps, status split.
- `dag/nodes/sec-poincare-duality/lem-pod-truncation-interchange-pentagon.json`: statement, Mathlib leaf. The underlying interval-truncation interchange, its normalization and uniqueness are `CategoryTheory.Triangulated.TStructure.truncGELTIsoLTGE` (TruncLTGE.lean:889), `truncGELTToLTGE_app_pentagon` (:808) and `truncGELTToLTGE_app_pentagon_uniqueness` (:813), with the same full namespace. All three specialize by replacing Mathlib's strict upper cutoff with b+1. No proof is added to the leaf.
- `citations.json`: one entry for each of the sixteen proof-step citations; quotes checked verbatim against the cited statements.

## Attachments

None. Searched the project Lean sources under `lean/WeilConjectures/` for the exact blueprint tag, fixed-pair terminology, and Postnikov terminology. The returned occurrences concerned section-map pairs, finite etale pairs, and an unrelated Postnikov argument. No project declaration states this item, so there is no ATTACH claim. The Mathlib result is recorded as a leaf rather than as an attachment.

## Wanted literature

None. Read the local BBD PDF, Proposition 1.3.3 and paragraphs 1.3.4–1.3.5, printed pp. 29–31 (PDF pages 30–32), and the current `main-20261015` blueprint `prop-weil-operations.proof.md`, sentence 2, and the truncation/cohomology clause of `prop-weil-operations.md`. The abstract shift and fixed-pair calculations are supplied by the worker and are marked agent-origin. No SGA reference is used. No Stacks tag states the abstract t-structure interchange: the Stacks complex-truncation results concern a specific derived category, whereas this item allows an arbitrary triangulated category and t-structure.

## Corrections and scope

The live item had a complete statement but no proof. Its statement, source, inherited searches, created metadata and blueprint provenance are retained. There is no released repair note and no earlier sandbox item or report. The parent and unit were read: this is the generic categorical component of the operations clause, not the key statement of `sk-lem-finite`, so no unit binding is changed. The chapter and unit route remain unchanged.

The existing heart theorem says that the two truncations canonically commute but does not state the normalizing pentagon. Citing its proof to obtain that equation would violate C3/C4. The new Mathlib leaf exposes exactly the isomorphism, equation and uniqueness actually needed. Absorption does not need a new node: its inverse maps and identities follow immediately from the already cited adjunction bijections. Likewise shift lifting, composing the two lifts, and cancelling two shifts are written as equations in the item, not extracted as lemma nodes.

## Not duplicates

lem-pod-truncation-interchange-pentagon vs lem-weil-heart-short-exact-triangles: the latter's clause 1 asserts canonical interchange at degree zero, without its defining diagram or its uniqueness as a morphism satisfying that diagram. The leaf states the normalized pentagon for all intervals a<=b, and the unique-morphism characterization; Step 6 uses that characterization, not just existence of some isomorphism. This is a direct Mathlib interface, not a second proof of the heart theorem.

lem-pod-truncation-interchange-pentagon vs lem-pod-fixed-pair-postnikov-identifications: the leaf has no endofunctor, fixed pairs or shifted equivariant cohomology, and makes no equivariance assertion. The item's argument constructs the lift using fixed-pair adjunctions and proves that its underlying arrow is the leaf's normalized isomorphism. Thus the new node does not restate a clause with its equivariance suppressed as an unproved surrogate.

lem-pod-truncation-interchange-pentagon vs lem-pod-texact-truncation-comparison: that node compares an exact functor with a single truncation; it states no interchange of two truncations and no interchange pentagon.

Searched the whole DAG for absorption, interchange, truncation adjunctions, the Mathlib declaration names and their pentagon terminology. Read the statements of the relevant existing nodes. Whole-blueprint searches were run for truncation, absorption, interchange, fixed pairs, truncGELT and truncations commute. No existing blueprint node states this normalized characterization; `same_as` is empty. The new leaf and item both descend from `prop-weil-operations` through the recorded `via` chains. No shared Stacks tag pair needs disambiguation.

## Mathlib searches

All new searches were run using the required `msearch.py` command and read from its output. `searches.jsonl` is retained. For the item, LeanFinder in two phrasings, LeanSearch, Loogle and grep found underlying truncation and shift infrastructure but no theorem covering the whole fixed-pair statement. For the leaf, two semantic phrasings plus LeanSearch returned generic truncation/triangle material; Loogle for `"truncGELTToLTGE"` found the pentagon and uniqueness explicitly. Grep located the definition and normalization, then a second grep located uniqueness at line 813 and the natural isomorphism at line 889. I read TruncLTGE.lean:700–905 and the reindexing definitions in TruncLEGT.lean:38,81,404. The natural isomorphism's hom is the displayed natural transformation, not an unrelated choice. The `mathlib_match.how` names the declaration and line of every clause. Semantic results are recorded as no direct match, not attributed invented hits. None of these services was unavailable.

## Review by Q16

I read BBD's actual argument, not only the imported references. In 1.3.3 the adjunction bijections characterize the two truncations; 1.3.4 gives the nested absorption maps; 1.3.5 constructs interchange by two adjunction factorizations and proves the resulting arrow invertible. For the new node I checked its entire normalized statement against Mathlib's pentagon equation, uniqueness lemma and natural isomorphism, including the b+1 reindexing for non-strict upper truncation. The source's a<=b hypothesis is retained even though Mathlib's result holds more generally.

For Step 1 I checked the morphism condition in `def-weil-endofunctor-fixed-pair-category` and the actual shift notion in `def-weil-triangulated-category`. The displayed equation uses naturality of the assumed s, with domain P(K[r]) and codomain L[r]. It proves equivariance directly; no exactness or t-exactness of the shift relative to a fixed cutoff is falsely assumed.

For Step 2 I read `lem-a1-fixed-pair-truncation-orthogonality`: it really asserts lifted functors on underlying truncations and arrows. I also read the normalized comparison equations in `lem-pod-texact-truncation-comparison`. Composing those lifts gives R(L(theta)c-)c+, so functoriality expands it to RL(theta)R(c-)c+. Shifting that expression produces exactly the stated e, with every factor's domain and order checked. This uses the supplied natural comparisons, not an unstated theorem about equivariant Postnikov triangles.

For Step 3 the cited new leaf says the actual objects R_i L_i K and L_i R_i K are isomorphic. The original definition of t-structure explicitly makes its halves strictly full and gives the truncation bounds. Therefore the former has both bounds i. The same definition's shifted-half convention gives the heart membership after [i]. This does not require equivariance of interchange yet; Step 6 proves that separately.

For Steps 4 and 5 I checked that the fixed-pair lemma states the right and left adjunctions for every integer cutoff, not just ordinary-category adjunctions. The source definition gives the nested inclusions needed to apply them twice. The upper argument tests objects in <=m-1; the lower tests objects in >=m+1. In both cases the text constructs maps in both directions and obtains their inverse identities from injectivity of composition or precomposition. The comparison with the canonical underlying maps follows from the same underlying adjunction. These are short consequences of the cited statements, not new unproved absorption lemmas. The adjunction's naturality proves naturality in K.

For Step 6 I checked the hypotheses separately: RK is in >=m, while A_K is in <=m by Step 3. Thus the two factorizations are allowed in the fixed-pair adjunctions. Their composite satisfies exactly the leaf's pentagon. The leaf's uniqueness identifies that arrow, rather than an arbitrary isomorphism, with the canonical interchange. Its inverse is equivariant by the inverse equation written in the step; this uses the fixed-pair morphism definition. Naturality follows from naturality of transposition, so no unsupported assertion that a diagram 'transports' is left.

For Step 7 I checked shift direction: H^m=Z[m], so the comparison to H^m[-m] uses the inverse of cancellation Z[m][-m]->Z. Coherence of s gives the explicitly displayed cancellation identity with P(d_Z), and naturality of d_Z gives its equivariance. This checks the structure after both shifts, not only an isomorphism of underlying objects. Composing with inverse interchange gives the second identification with precisely the same shifted cohomology structure.

All hypotheses of the reused generic lemmas are supplied: P and its inverse are exact and preserve both halves, so the fixed-pair adjunction lemma applies at every cutoff; boundedness in the item supplies the boundedness needed by the comparison lemma. The only off-unit non-Mathlib generic tool used is `lem-a1-fixed-pair-truncation-orthogonality`; it is declared in `split_report.tool_uses` because this unit has no duplicate of the fixed-pair adjunction statement. No top-level maintainer-owned tool_uses field is written.

I checked B–E explicitly: the new leaf introduces every object, has its notion dependencies and no proof; its source is the correct BBD proposition rather than an inapplicable Stacks tag; its Mathlib match cites actual lines. Each non-elementary item step cites the statements providing its input, and the elementary steps show the equations. The new leaf is neither the item nor a new equivariance clause. All comparison equations are typed on objects in the needed halves. No comparison is defined only degree by degree. Every step is under 2000 characters and no standard intermediate theorem is hidden in a long paragraph.

Small cases checked: the zero category and zero object; P=id with arbitrary automorphism theta; r=0 and r negative; K=A[-m] concentrated in degree m; and truncation cutoffs outside K's bounded support. On a single-degree object the cohomology is A, and the opposite shift cancels to A[-m], confirming the sign. Absorption is identity on already truncated objects and remains the zero-object isomorphism on a killed piece. The interchange pentagon at a=b is the source's valid endpoint case. No nondegeneracy or triangle structure on pairs is needed. I found no statement dispute.

## Unfinished work

None in this stage-1 item. The existing statement is preserved and the sole new node is already a Mathlib leaf. Delivery is subject to the required server dry run and independent maintainer review.

## Dry-run repair

The first server preflight required a dedicated `mathlib_match.line` field in addition to the verified lines already written in `how`. Added line 889 for the main natural-isomorphism declaration; the normalization and uniqueness lines remain explicit in `how`. No mathematical statement or proof changed.
