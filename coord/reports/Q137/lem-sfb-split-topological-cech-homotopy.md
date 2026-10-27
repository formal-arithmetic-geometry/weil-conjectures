## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-split-topological-cech-homotopy.json`: existing statement split into six elementary steps; original statement and statement dependencies retained. Mathlib searches find no direct match.
- `citations.json`: empty list, because every step is an explicit calculation from the definitions in the item and has `uses: []`.
- `searches.jsonl`: actual search-command records for this item; existing historical searches in the live node are preserved as well.

## New nodes

None (0 new nodes, 0 Mathlib leaves). The continuity verifications, face calculations and finite signed cancellation are short elementary arguments, and are written in the item instead of creating nodes for its clauses.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint docstring tag and for Cech/homotopy/contraction terminology. `AlgebraicTopology.setCechNerve` and its private `homotopy_identity` in `AlgebraicTopology/SetCechNerveFreeResolution.lean` concern free modules on a set nerve. They do not assert the continuous-function statement for a general topological abelian group. The site free resolution and alternating sheaf contractions likewise concern different objects, not all clauses of this item.

## Literature and WANTED

Read the current blueprint `main-20261015/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), and its unit statement, and `literature/stacks-project/simplicial.tex`, Tag 016E, label `example-fibre-products-simplicial-object`, lines 308–319. The latter defines the fibre-product nerve by coordinate selection; it does not prove the homotopy. The analytic auxiliary is already identified as agent-created by the item's source, and the new proof is expressly `proof_origin.by = agent`. No additional document is needed for the elementary calculation; no WANTED request.

## Existing-node and Mathlib searches

Whole-DAG searches covered Tag 016E, extra-coordinate, split topological, continuous cochains, and precomposition. Whole-blueprint searches with `tools/blueprint_refs.py search` covered `extra-coordinate`, `contracting homotopy`, and `Cech`. Read the nearby statements `def-sfb-set-cech-nerve`, `lem-exc-coinduced-homotopy-identity`, `lem-sfb-equivariant-continuous-cochain-prism`, and the parent `lem-sfb-norm-algcl-profinite-cech-exact`. They respectively define a set nerve, contract particular discrete coinduced group cochains, give an equivariant field-valued prism formula, and use this item for the split-cover case. None supplies this exact general topological assertion without another comparison or circularity. No node is created.

Ran msearch LeanFinder with two phrasings (continuous section insertion; then prepending a section and the signed identity), Loogle for `"cech", "homotopy"`, LeanSearch for the alternating differential on continuous functions, and greps for extra degeneracy and contracting homotopy. Read their hits: generic cochain homotopy constructors, group cochain formulas and alternating multilinear maps do not state this assertion. In Mathlib `AlgebraicTopology/ExtraDegeneracy.lean` read lines 331–440: `CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy` at 368 gives a categorical extra degeneracy; `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` at 415 gives a chain homotopy equivalence in a preadditive category. Identifying these categorical limits and their dual complex with the displayed subspaces and all continuous A-valued functions is additional work, so the inherited candidate remains a candidate, not a Mathlib leaf. Every added search entry is copied from the actual search log, with identical tool and query. There were no unavailable services in these new searches.

## Problems found and changes

The original item was unsplit with an empty proof. Its mathematical statement is correct, including positive degree one and empty spaces. No statement correction was made. The essential detail made explicit is the face deleting the original coordinate zero: its inserted value is initially written using the new first entry t_1, and equals the old inserted value by equality of the q-images. Omitting this detail would leave the cancellation unjustified.

The inherited blueprint ancestor chain reports `None` in `blueprint_refs.py ancestor`, because a preceding created.item chain ends at a module identifier. Retained the existing from.node=null and via chain, with the precise source paragraph and auxiliary role already written in from.place. The blueprint paragraph motivates the auxiliary but does not itself state it; the report and proof_origin make that distinction explicit. No other node or maintainer field was edited.

## Review by Q137

I read the item and each of its six saved proof steps against the source places above. This is the direct-delivery self-review authorized by this brief; no second worker or agent was started.

Step 1 proves that the deletion and insertion rules have the asserted codomains: retained coordinates still have equal q-images, and the new one has that same image because q sigma is the identity. This uses only the hypotheses in the item, never surjectivity as an extra hypothesis or a chosen point. There is no cited node whose statement is being asked to supply this calculation.

Step 2 proves continuity by cylinder opens, finite intersections, unions and the subspace definition. The insertion's first component uses exactly the assumed continuity of q and sigma. No quotient-map criterion, closed-subspace assumption, categorical limit comparison or separation hypothesis is used. The argument proves continuity of the actual tuple map rather than referring to a nerve definition as if it implied a theorem.

Step 3 checks that the expressions land in the continuous-function groups. The pair-map rectangle computation and continuity of addition give pointwise addition; negation uses its explicit hypothesis. Continuity of composites is the inverse-image identity. Finite iteration suffices for the signed sum; additivity of h is checked by evaluation. Neither topology on the function group nor completeness is used, and no non-elementary functional-analytic fact is hidden here.

Step 4 lists the face-insertion identities on every coordinate. I checked the indices: x has n+1 entries, s(x) has n+2, and deleting j+1 corresponds to deleting original entry j. For j=0, n>=1 ensures t_1 exists, and equality of its q-image with q(t_0) proves equality of inserted values. This is the delicate hypothesis check; it is written explicitly in the saved proof.

Step 5 uses exactly those tuple equalities to expand both composites. Its first sum has j=0,...,n with sign (-1)^j; the second has the isolated f(x) and matching terms with sign (-1)^(j+1). Commutativity of A and cancellation of opposite terms give equality pointwise, hence equality of continuous functions. This is the proof itself, not an application of a new node repeating the conclusion. Every summand is identified; nothing is hidden under a compatibility assertion.

Step 6 tests n=1 with all three terms of d^1 shown and verifies the two empty-space implications using the given maps. It also checks that no compactness, separation, metrizability or completeness entered any prior step. For a singleton T and V all face values coincide, and the signed sums alternate between identity and zero as required; for the zero coefficient group every map and equation is trivial. With q=id, tuple spaces are diagonals and the same parity check applies. No nonemptiness or characteristic restriction was introduced.

I checked B1–B10: there are no new nodes; the original self-contained statement and correct single TeX escapes are retained; the source Tag 016E is used only for nerve background; no unsupported leaf or attachment is claimed; existing searches and provenance survive. For C1–C8 every use is elementary and fully written in its step, with no citations beyond their statements, missing imported lemma, off-route tool, or new cycle. `citations.json=[]` agrees with all six empty `uses` lists. For D1–D5 the argument stays in the item, with no clause-restating helper or circular call to the parent. For E1–E7 the coordinate-zero case, correct source/target lengths, signs, n=1, empty spaces, zero group and identity map were checked above. All six steps are under 800 characters, hence none crosses the 2000-character long-step review threshold. The source supplies no false claim that has to be repaired. The mathematical review is complete; validation and delivery use the required delivery tool.

## Not duplicates

No new nodes; no new/existing node pairs require distinction.

## Unfinished work

None in this one-level stage-1 split. No Lean was written and no compiler, Lake or build tool was run.

## Resumed validation

Continued the saved split and searches, compared every changed field with the current live unsplit node, and confirmed there is no released repair note. Re-read the current blueprint paragraph (3), the recorded unit and chapter, Stacks Tag 016E, the upstream set-nerve homotopy, and the Mathlib extra-degeneracy candidate. The saved six-step argument remains valid and needs no new lemma. The first resumed dry run rejected the phrase “No pending mathematical work remains” because the report gate treats the word “pending” as an unfinished review, including under negation. Replaced that sentence with an explicit statement that the mathematical review is complete. No mathematical statement, proof, citation or search was changed.

## Repair of returned delivery 3cd8d8f48e4

The 2026-10-22 return says the reader approved the split, but landing refused the side-project completion because the queue reads the live DAG. This repair retains the returned sandbox proof and all searches rather than treating the side completion as a live landing. I compared every field of the retained node with the current shared DAG: the current item is unsplit, with an empty proof and no review; its statement, statement dependencies, source, blueprint data, chapter, unit, creation metadata and Lean audit agree with the retained version. The differences are precisely the delivered split, proof provenance, split report and additional recorded searches. There is no released repair note. The required delivery tool rebuilds the delivery on the current DAG; the initial resumed dry run passed at ebcc7c98c3c.

The sole statement dependency is def-weil-size-convention. I opened its current statement, which fixes universes and small skeleta, and confirmed that the item's opening universe convention is all that is taken from it. There are no proof citations to rebase, substitute or quote: all six proof uses lists are empty and citations.json remains []. In particular, neither the parent exactness theorem nor a changed comparison lemma enters this proof. I re-read the current main-20261015 unit and its direct-images paragraph (3), Stacks Tag 016E with its tag-to-label mapping, the upstream set-nerve free-module contraction, and the Mathlib extra-degeneracy candidate; none supplies a new exact attachment or changes the elementary continuous-function argument. Existing searches were read and reused, with no new search claim.

I adjusted step 4 to distinguish the deletion maps by the length of their target, writing p_j^(r): X_(r+1) -> X_r, and explicitly checked both compositions have domain X_(n+1) and codomain X_(n+1). This also records exactly where n >= 1 is needed for the coordinate-zero deletion. Step 5 now uses those indexed faces and names b_j, so opposite parity gives -b_j and the final finite sum is explicitly the sum of b_j + (-b_j). These are mathematical clarifications of the saved proof, beyond a rebase or unchanged re-push. They introduce no new hypothesis, definition or helper node. The lowest-degree calculation and empty-space argument in step 6 still agree with both indexed composites.

I rechecked delivery-errors B through E for this repair. There are no new statements or leaves to audit, no non-elementary comparison is hidden in a step, no proof dependency or cycle is added, and all six steps stay below 2000 characters. The topology argument uses only the supplied continuous q, section and group operations. The index and parity changes were checked against n=1, the identity map, empty spaces and the zero group. No statement dispute arises. Only the sandbox item and this report were edited; the source repository and launcher were read only. The final dry run and push use the required delivery tool sequentially.
