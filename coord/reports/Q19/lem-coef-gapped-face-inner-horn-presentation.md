## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-coef-gapped-face-inner-horn-presentation.json`: statement, now split in seven steps; no exact Mathlib match or one-line specialization found.
- `citations.json`: verbatim statement excerpts for each of the four node citations, in steps 1, 4, 5 and 7.
- `searches.jsonl`: six actual Q19 search results, supplementing the eight historical searches retained in the item.
- `check_cases.py` and `case-check.txt`: finite combinatorial validation of the filtration.

New nodes: none. Mathlib leaves: none. The original statement, statement dependency, creation provenance and blueprint ancestry are retained. `prepare_split.py` records the sandbox-only preparation. No Lean file was written and no compiler, Lake or build command was run.

Attachments: none. Searches under both read-only `WeilConjectures/` source trees for the exact blueprint id and for gapped faces, generalized horns, finite horn filtrations, inner horns and coherent weak retractions found no project declaration stating this item. The upstream master source is reference material, not completion evidence. The item has no `lean_audit` declarations to inspect; no sorry-free attachment was claimed.

WANTED: Jacob Lurie, *Higher Topos Theory*, Lemma 4.4.5.8 and proof, printed pp.305–306, PDF zero-based page indices 322–323, for lem-coef-gapped-face-inner-horn-presentation. I read the online author-hosted PDF at https://www.math.ias.edu/~lurie/papers/HTT.pdf, but it is not archived in this repository's literature. Accordingly `proof_origin.by` remains `agent`, with the source and the expanded argument specified. No Stacks tag for this finite simplicial combinatorial statement was found; none is invented.

What was wrong or incomplete: the seeded item was statement-only, rather than a completed split. The displayed pushout square in HTT needs an explicit verification that the distinguished face is not already present; steps 3–6 supply the positive facet membership, negative distinguished-face membership, all-degree intersection, and actual degreewise gluing. The statement agrees with the source, including the gap hypothesis and exact restriction in the consequence, so no statement dispute or correction is needed. I did not infer finite horn presentations merely from an inner-anodyne classification, which would only give retracts of potentially infinite cell constructions.

Unfinished work: none in the requested stage-1 split. The second reader must independently inspect this sandbox and perform delivery; this worker performs only the prescribed no-push dry run.

## Sources, route and searches

I read `dag/chapters/sec-six-functors.json` and `dag/units/sk-prop-sf-biduality-general.json`, the item's historical blueprint ancestry, the current main-20261015 `prop-coef-integral-exceptional-adjoint.proof.md` paragraph containing the finite-coefficient mapping-complex adjunction, and the parent `lem-coef-weak-retraction-coherent-extension` statement and step 3. The latter applies this item with n=2m, J the odd vertices, and gap 1<2<3. This delivery supplies exactly that finite combinatorial tool below the historical ancestry. It replaces no unit step and changes no chapter or unit record. The only cited node is a definition, so no off-unit theorem tool declaration is required. No SGA source is used.

Before deciding whether any new node was needed I searched the whole DAG by the exact HTT number, gapped/generalized horns and finite inner-horn filtrations, and ran `tools/blueprint_refs.py search` for gapped, finite horn, Lemma 4.4.5.8 and faces which do not contain. No blueprint duplicate was returned. I opened `lem-coef-inner-horn-cell-generation`, `lem-coef-twisted-arrow-join-horn` and `lem-coef-spine-cancellation-inner-horns`. The first classifies general inner-anodyne lifting maps as retracts of transfinite cells, rather than giving this finite filtration; the second treats paired vertex deletions in two blocks; the third is a saturation/cancellation criterion starting from spines. None states this item. The elementary set and gluing arguments need no separate new nodes. No new-node duplicate pairs arise.

The six new logged searches use LeanFinder (two distinct phrasings), Loogle, LeanSearch and two Mathlib grep patterns. All services returned successfully, so none is marked unavailable. I read the actual hits and the pinned Mathlib sources: `Horn.lean:32–62`, `Quasicategory/Basic.lean:39–53`, `AnodyneExtensions/Inner/Basic.lean:43–60,89–92,143–157`, `AnodyneExtensions/PairingCore.lean:203–234`, and `AnodyneExtensions/Inner/PushoutProduct.lean:55–61`. Horn definitions and filling are single-cell primitives; the pairing result assumes an already supplied regular inner pairing; the product result concerns a horn times a boundary. These results do not give this finite gapped-face presentation in one line. Historical Q09 and second-reader searches and their recorded results were retained rather than rewritten as Q19 searches.

## Not duplicates

No new nodes were created. The nearby horn statements listed above concern different domains or a general retract/transfinite criterion; this item's finite cardinality-ordered face attachment is written in its own proof.

## Review by Q19

I checked the statement against HTT Lemma 4.4.5.8 and its actual proof, not just its conclusion. HTT's K consists of the simplices not containing the face on J; in a standard simplex this means their image omits some vertex of J, exactly the item's union of codimension-one faces indexed by J. Both hypotheses require i,k in J and j outside J with i<j<k. HTT enumerates the supersets of J union {j} compatibly with inclusion. Sorting by cardinality realizes that enumeration and makes every earlier set have cardinality at most that of the current set. The source's pushout proof gives the stronger finite-presentation clause already in this item; the final extension clause follows from the explicit quasicategory definition, with no uniqueness claim.

I opened the complete statement of `def-cbc-enhanced-diagrams-cones`. It expressly defines the standard simplex by monotone maps and precomposition, the horn by omission of some vertex other than its index, and a quasicategory by exact extension of every inner-horn map. These are the only three pieces cited, and their exact sentences are in `citations.json`; step 4 also cites the standard-simplex convention for its direct face-membership calculation.

For step 1, the definition node supplies the standard-simplex and operator conventions; membership in the item's spanned face and union then follows directly by images. This proves stability under every simplicial operator, including those producing degeneracies. For step 2, the finite collection P and cardinality ordering are constructed from the finite vertex set; the unique largest subset is the full set, so the endpoint is the whole simplex. This is finite set combinatorics, with no external existence or colimit lemma.

For step 3, I checked both alternatives for each v different from j: deleting v in J puts the face in K_J; deleting v outside J leaves J and j and gives an earlier member of P. The vertices i,j,k are still in every attached T before deletion, which proves both d>=2 and the strict inner-index inequalities. For step 4, F=T minus {j} still contains J precisely because j is not in J. Any earlier T_b containing F must also contain j, hence T; cardinality then forces equality, contradicting the distinct enumeration. This proves absence of the distinguished face rather than assuming it from a picture. These are direct arguments establishing this item's filtration, not uses of an unnamed generic filtration theorem.

For step 5, the cited definition's omission-of-a-nondistinguished-vertex criterion is exactly the horn criterion used. I checked the converse for an arbitrary monotone map: if its image contains all vertices other than j it is F or T, and no earlier union part can contain that image. Thus the intersection is exact in every degree; checking only codimension-one injective faces would have been insufficient without this image argument. For step 6, the two maps agree on the full intersection and therefore glue degreewise, and precomposition preserves each part; these statements establish both the set pushout and its simplicial operators directly. No presheaf-colimit theorem or monomorphism saturation theorem is silently used.

For step 7, the cited node's actual statement guarantees an extension of each inner-horn map. The dimensions and inequalities were established in step 3. The step-6 pushout gives a map whose restriction to the previous stage is exactly the old map. The induction starts at the specified f_0 and has finitely many stages, so its endpoint has the requested exact restriction. No Kan, nonempty target, colimits in Q, uniqueness of fillers or outer-horn hypothesis is introduced.

I checked delivery-errors B–E against the files and source. There are no new unsplit nodes, clause restatements, circular dependencies or new Mathlib leaves to justify; the item carries the construction itself. Every cited node's statement says exactly what is used, and every other operation is an explicit finite-set calculation or set gluing, not an unquoted theorem from a cited proof. Steps 4 and 5 are marked non-elementary because they carry the substantive exclusion and intersection argument; their proofs are fully written. The longest step is 753 characters, so no step exceeds the 2000-character long-step review threshold and no auxiliary standard comparison is hidden in one.

Small cases: for n=2, J={0,2}, j=1, P contains just {0,1,2}, so the construction is exactly the attachment of Lambda^2_1. For n=3, J={0,3}, j=1, the first face is {0,1,3}, attached along its inner 2-horn, and then the full tetrahedron is attached along the inner horn at vertex 1. For n=4, J={1,3}, j=2, all four supersets of {1,2,3} attach in cardinality order. The gap excludes J empty, a singleton and every interval J; no conclusion about outer horns follows. An empty Q creates no exception: K_J has vertices, so no input map exists. I also ran an exhaustive Python check of every J and every admissible j in dimensions 2 through 8, comparing the intersection with the exact inner-horn supports and checking final coverage. See `case-check.txt` for the checked counts. This checks the combinatorial claims without compiling Lean.

Corrections made during this review: none to the statement or source route. I supplied the previously missing proof, selected the explicit degreewise argument so that no Eilenberg–Zilber decomposition is assumed, retained the honest source-archive request and historical searches, and added precise citations and the small-case verification.

## Dry run

The required no-push delivery dry run is run after this report is written. Its final result will be recorded here; no delivery push is authorized to this worker.

## Second reading by Q19

- Statement: checked against HTT Lemma 4.4.5.8, pp. 305–306 (PDF indices 322–323); the definition of (K), gap hypothesis, and inner-anodyne conclusion agree exactly, with the extension consequence correctly derived from the quasicategory horn-filling definition; verdict PASS.
- Step 1: checked against the standard-simplex and horn clauses of `def-cbc-enhanced-diagrams-cones` and HTT's description of (K); image containment and closure under operators also cover degeneracies; verdict PASS.
- Step 2: checked against HTT's collection (P) and (K(k)) construction; cardinality order is a valid inclusion-compatible finite order and reaches (Delta^n); verdict PASS.
- Step 3: checked against HTT's attaching-face argument; deletion of a (J)-vertex lands in (K_J), deletion of another vertex is an earlier member, and the gap gives an inner index; verdict PASS.
- Step 4: checked against the omitted (j)-face argument in HTT; the containment and cardinality comparison correctly exclude both (F) and (T) from the previous stage; verdict PASS.
- Step 5: checked in every simplicial degree against the horn definition in `def-cbc-enhanced-diagrams-cones`; the image (F) or (T) converse establishes the exact intersection, including degenerate simplices; verdict PASS.
- Step 6: checked against HTT's pushout square and the explicit degreewise gluing argument; the induced operators and universal map are justified; verdict PASS.
- Step 7: checked against the quasicategory definition in `def-cbc-enhanced-diagrams-cones`; finite induction gives fillers agreeing exactly on (K_J), with no extra hypotheses; verdict PASS.
- New nodes: none; no duplicate, elementary, restatement, or Mathlib-leaf node was introduced, so there are no new-node statements to audit.
- Citations and dependencies: all four citation quotes are verbatim from `def-cbc-enhanced-diagrams-cones`, and every non-elementary fact used by a step is covered by its cited statement; verdict PASS.
- Small cases and searches: reran the finite checker (2,116 admissible cases for (2\le n\le8), 30,748 exact intersections) and added fresh LeanFinder, Loogle, and grep searches; no exact Mathlib declaration or one-line specialization was found; verdict PASS.

Changes made: none to the statement, proof steps, dependencies, source route, or citations. Added only the second-reader audit above and the three fresh search records required for independent verification.

## Dry run result

`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q19 lem-coef-gapped-face-inner-horn-presentation --no-push .` passed: `OK (not pushed) deliver/Q19/lem-coef-gapped-face-inner-horn-presentation at 835a531a26: preflight passed`.
