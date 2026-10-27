## Worker report

### Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-poset-weak-prism-identity.json`: item, status split; unchanged statement and statement dependency; seven explicit elementary steps, 2688 characters in total. No exact Mathlib match.
- `citations.json`: the single dependency quotation, for step 1, checked verbatim against its node statement.
- `searches.jsonl`: recorded by the prescribed msearch command; six searches made in this session. Earlier searches in the item's repository record are retained.
- `check_small_cases.py`: sandbox-only finite integer-coefficient check of the formula and repeated-tuple inclusion. Not a Lean file, and not part of the delivery's node changes.

New nodes: 0. Mathlib leaves: 0.

### Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, weakPrism, weak prism, poset/prism combinations, weakly increasing, repeated tuples and vertex deletion found no declaration stating the item. Related alternating Cech declarations concern different complexes. No sorry-containing declaration was treated as a finished proof.

### WANTED

None. The relevant Stacks source is available locally.

### Findings and changes

The statement is correct and unchanged. Its proof was empty. The proof now spells out adjacent-repeat preservation, both off-junction deletion reindexings with their exact coefficients, junction telescoping, the degree-zero repeated pivot, the fixed empty generator and lower/empty cases. There is no appeal to a general simplicial homotopy theorem and no new node restating a clause of this item. All subclaims are immediate tuple computations or finite additive cancellation from the displayed definitions.

The ancestor command reports blueprint.from.node = None. The existing ancestor chain in blueprint.from.via and the contextual place have been retained, and the place is now explicitly checked against the latest blueprint. This tool was introduced below the old direct-image route; the blueprint does not itself state the combinatorial prism. The latest direct-images proof still has the relevant open-image paragraph (3), although it routes through the coefficient preservation results rather than spelling out this finite calculation. No chapter or unit record is changed.

### Unfinished work

None for this split. Acceptance and independent mathematical review belong to the maintainer.

## Not duplicates

No new nodes were created. Searches of the whole DAG for Tag 019S, prism, weakly increasing and repeated tuples were read. The parent `lem-sfb-poset-augmented-chain-prism` is the strict-chain quotient theorem and already depends on this item: it cannot be cited back. Its sibling `lem-sfb-poset-weak-chain-normalization` concerns the differential, quotient by repetitions and functoriality, not the prism identity. `lem-weil-pbc-simplicial-homotopy-free-chain-homotopy` only supplies existence of a homotopy given a simplicial homotopy, and does not identify this formula, augmented degree or repeated-tuple inclusion. `lem-trf-coefficient-bar-prism-homotopy` concerns categorical coefficient bar complexes, without this augmented weak-poset basis or repetition assertion; `lem-sfb-equivariant-continuous-cochain-prism` is a cochain formula for continuous equivariant functions. None supplies a direct attachment or replaces the explicit elementary calculation. Whole-blueprint searches `prism` and `weakly increasing` each returned zero matches.

## Mathlib searches read

The prescribed msearch commands ran leanfinder twice with different natural-language phrasings, loogle with the comma-separated pattern `"SimplicialObject", "Homotopy", "toChainHomotopy"`, grep twice in AlgebraicTopology, and leansearch once. All services answered successfully. Exact query strings and returned log summaries are copied into the item's mathlib_searches, with today's date and a verdict. All earlier query records were retained.

Read Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean:39–47,156–160: the homotopy component is a negative signed sum and requires an already constructed simplicial homotopy. Read DoldKan/HomotopyEquivalence.lean:50–73: its homotopyPInftyToId normalizes one simplicial object. Read SimplicialSet/Homology/Nondegenerate.lean:38–50: its chain complexes are indexed by natural numbers and it constructs normalization maps. The other hits Rep.standardComplex.d, d_of and AlternatingFaceMapComplex.objD only give a differential, not this prism. Constructing the poset simplicial homotopy, identifying the stated positive formula, proving repeated-tuple preservation and augmentation would be additional work, so these do not make the item a Mathlib leaf.

## Review by ND

I read Stacks `simplicial.tex`, Tag 019S, `lemma-homotopy-s-N`, and the preceding `equation-homotopy-to-homotopy`, lines 4739–4848. Its computation splits the boundary into four sums and leaves the outer cancellations to the reader. Here the tuple formulas perform those cancellations explicitly. The source uses the negative prism sum and concludes a-b; the item uses the positive sum and concludes g-f. The signs in steps 4–6 have been checked directly, rather than imported with the source's convention. The source is only an unaugmented additive-category result: repetition preservation and augmented degrees are additional explicit arguments here, and proof_origin remains agent. There are no new nodes whose statements require separate literature justification.

I read the chapter and unit records and the latest blueprint chapter and the stability proof/direct-images proof, specifically paragraph (3) concerning proper and open direct image. The finite combinatorial tool remains below the inherited route; this split neither modifies that route nor claims that the source paragraph contains this argument. The null blueprint ancestor is recorded openly rather than replaced by an invented id.

Step 1 uses exactly `def-weil-pbc-module-chain-complex-homology` for d_n landing in degree n-1. I opened that node and copied the actual sentence giving this convention into citations.json; I do not use its homology or chain-map clauses. Equality on the explicitly supplied free-module basis follows by linear extension, not a hidden homological-algebra result.

Step 2 uses only monotonicity and the pointwise inequality at the pivot: these are precisely hypotheses of the statement. Antisymmetry and the intervening inequalities show that any repeated weak tuple has an adjacent repeated pair. No strictness or injectivity of f or g is assumed. Step 3 checks both possible pivot positions relative to that adjacent pair; the equality is retained either in the g segment or the f segment. In particular, the pivot sitting between the equal vertices is covered by the second case. This proves the inclusion on generators, then on their span. D_n=0 handles n<=0. These two steps cite no theorem because the entire argument is written from the tuple definitions.

Step 4 pairs each deletion j<i with the identical tuple from deleting x_j first and using pivot i-1; its exponents differ by one. Step 5 pairs j>i+1 with deleting x_{j-1} first and using pivot i; again the exponents differ by one. The inverse assignments for every (k,r) in Hd are displayed, with k<=r and k>r as the exhaustive alternatives. These statements are direct equality of lists and signs, so no uncited simplicial identity is being used. Terms are paired as indexed summands even when their underlying basis tuples coincide; repetitions are never killed in W.

Step 6 accounts for both unpaired faces of each prism. The cut tuple A_i includes the empty f segment at i=0 and the empty g segment at i=n+1; the signs are respectively +1 and -1. The finite telescoping sum has precisely the g endpoint minus the f endpoint. This is additive cancellation in a free module, valid in every commutative ring, including characteristic two and the zero ring. No quotient identification, normalization theorem or homology theorem is used.

Step 7 separately checks n=0, f(x)=g(x), n=-1, n<-1 and the empty-poset possibilities. The weak repeated tuple [f(x),f(x)] remains a basis tuple; its boundary is the difference of two equal vertices, not an illicit strict-chain convention. Both maps fix the empty generator, so their difference in degree -1 is zero even if P is empty. If Q is empty the given map f forces P empty, so no missing nonnegative basis case arises.

As an independent check of the sign/index calculations, the sandbox Python script exhaustively checked 4193 integer-coefficient basis calculations for chains of sizes 0–3 and the branching poset with two incomparable points above a minimum, all comparable monotone self-map pairs and weak tuples of lengths 0–5. It also checked weak increase of every output tuple and repeated output for every repeated input. All passed, including the unique empty tuple in degree -1. Integer coefficient identities reduce to arbitrary rings; the proof itself covers every poset and degree, not only these examples. Degrees below -1 were checked from the zero-module convention. No Lean/compiler/Lake tool was run.

For delivery-errors B–E: there are no newly invented nodes or notions, no unintroduced objects, no changes of statement, no doubled TeX, no dubious Mathlib leaf or unstated unavailable service, and no dependency cycle is introduced. The only cited statement is quoted literally; all other steps are explicit elementary tuple equalities. The proof is carried here, not moved into a clause node or a purported general theorem. Every step is under 2000 characters. I translated the source's negative prism convention to the item's positive convention and supplied both cancellations it leaves to the reader; nothing was weakened. No mathematical statement dispute remains.

## Repair of L's promotion refusal

L returned the delivery because its side-project completion had not been promoted to the live DAG read by the queue. I continued the retained delivered split rather than discarding its proof, citations, report or search history. The retained pre-repair receipt named commit `3101e46e8bb`; the mandatory initial dry run rebased that retained material against the current server state and passed at `4ea4d16dc27` (not pushed). That was diagnostic only; a new final dry run follows the changes below.

I compared every field of the sandbox item against the current shared `sheaf-dag` item. The current item is `unsplit` with an empty proof; its statement, statement dependency, source, title, chapter, unit and creation record agree with the retained delivery. Its only changes needed for this delivery are the worker-owned split fields and the previously checked blueprint place. I reconstructed the sandbox record from the current shared record and overlaid those split fields, retaining all current maintainer-owned fields.

There is one cited node, `def-weil-pbc-module-chain-complex-homology`. I re-read its complete current statement and its Mathlib match. It still states that an integer-degree differential is an R-linear map from C_n to C_(n-1), exactly the convention used in step 1; it remains a Mathlib leaf. The verbatim sentence retained in `citations.json` is still a substring of the current statement. No changed dependency hypothesis or conclusion requires a different proof. Steps 2–7 continue to use only the tuple definitions and explicit finite additive cancellation; no other cited statement needs migration.

I strengthened the actual proof text in this repair: step 4 now writes both double sums, including the full ranges of the deletion and pivot indices for Hd; step 5 explicitly checks the strict inequalities and bounds for the inverse reindexing. Thus the repair includes a reviewed proof adjustment as well as a rebase. I re-read Stacks Tag 019S and the latest direct-images paragraph (3), repeated the project-source attachment and whole-blueprint searches, and inspected the previously logged Mathlib candidates. The statement and search question have not changed, so the original search log and verdicts are reused without inventing or rerunning searches.

The retained small-case script passed all 4193 integer-coefficient calculations again. I verified the citation quote, equality of proof_deps with all step uses, the zero and negative degree arguments, preservation of repetitions for every pivot position, and the absence of any step over 2000 characters. No new node, Mathlib leaf, statement dispute or route change was introduced. This section supplements my signed Review by ND above with the current-base repair review.
