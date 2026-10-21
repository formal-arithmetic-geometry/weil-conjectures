# Stage-1 report: lem-sfb-simplex-lattice-shuffle-boundary

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-simplex-lattice-shuffle-boundary.json`: assigned statement, now split into ten explicit calculations; no exact Mathlib match.
- `citations.json`: the one node citation in step 1, quoted verbatim from its statement.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The existing chain-complex definition is already a Mathlib leaf. The logged searches are in `searches.jsonl`; its actual records are appended to the item's inherited `mathlib_searches` without discarding earlier searches.

## Attachments

None. A search throughout `lean/WeilConjectures/` for the exact blueprint tag, shuffle, and lattice-path terminology found only an unrelated internal-Hom evaluation shuffle and Koszul complementary permutation signs. Neither states any simplex-chain shuffle boundary identity. No finished project declaration was found.

## Wanted literature

WANTED: C. Weibel, *An Introduction to Homological Algebra*, section 8.5, the shuffle boundary calculation on unnormalized simplicial chains, for lem-sfb-simplex-lattice-shuffle-boundary. `literature/LIST.md` already lists the book as unavailable. No book text was read or claimed as authority. The supplied brief permits an agent-written proof while the source is unavailable; `proof_origin.by` is `agent`.

## What needed correction or completion

The assigned statement is correct as written; its hypotheses and conclusions are unchanged. The imported item had no proof. I supplied the word-indexed cancellation and all signs, including the four endpoints and zero-degree conventions. No statement dispute was found. The blueprint paragraph (3) motivates the direct-image comparison but contains no shuffle calculation; it is explicitly not treated as proof of this combinatorial result.

The unit record `sk-thm-sf-ctf-stability` is filed under the older six-functors chapter while the assigned node is filed under six-functors-basics. I preserved the item's chapter/unit and all inherited provenance. The blueprint ancestor command returns `None`, as the item's inherited `blueprint.from` already says; I did not invent a blueprint ancestor. Whole-blueprint searches for shuffle, lattice, and Eilenberg found no node stating this identity. Searches through all DAG nodes found the parent bicosimplicial comparison, its bar-comparison parent, and prism/cell lemmas; their statements concern different objects or depend on this input. None supplies or duplicates the explicit signed chain identity. No unit or chapter file is changed.

## Unfinished work

No mathematical clause remains unfinished in this one-level split. No Lean was written, compiled or built. The source book remains wanted as above. Independent maintainer review is still required after delivery.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs requiring disambiguation. The parent bicosimplicial-shuffle-totalization proves a homotopy-equivalence statement for bicosimplicial complexes using this universal boundary identity; it cannot be cited back here. The existing prism/cell statements do not assert the signed sum over all lattice paths.

## Review by Q13

I read `GOAL.md`, the three levels of SETUP, the stage-1 brief, worker role, stage document, and delivery-errors B–E (including their duplicated later copy). I read the assigned chapter and unit records, the assigned node's full statement and inherited searches, and the current blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially paragraph (3). This item is the universal combinatorial input beneath the prescribed direct-image route, not a replacement of any unit argument. There are no new nodes for which a source must be read. The proof is explicitly agent-written, rather than attributed to unavailable Weibel or to a blueprint that does not contain it.

For B and D, I checked that this is a proof rather than a renaming of its conclusion: no auxiliary node restates any clause, and no proof is hidden in an unsplit node. There are no new definitions or free-standing lemmas. Each of the ten steps is a direct finite-sum expansion, a short cancellation/reindexing, or an evaluation from the definitions in the statement; hence each is marked elementary. In particular the mixed-corner involution and horizontal/vertical sign changes are written out rather than called standard. Every step is shorter than 800 characters, so there is no long proof step hiding another comparison lemma.

For C1 and C4, I opened `def-weil-pbc-module-chain-complex-homology` and read its complete statement. Step 1 uses only its definition of a chain complex, and its convention extending nonnegative complexes by zero. It does not use any theorem about tensor exactness or homology. The requisite square-zero identity is proved in step 1 by the two orders of deletion, including the degree-one boundary into degree zero. The exact sentence concerning extension by zero is recorded in `citations.json` verbatim. All later steps use only the explicit groups, shuffle, inversion sign, and deletion formulas already introduced in this item's statement and in preceding calculations; they cite no external theorem. The proof-dependency union is therefore exactly this one definition node, already a Mathlib leaf.

Step 2 identifies each inversion in the concatenated permutation with a vertical letter before a horizontal letter; this verifies that the sign convention matches the statement, rather than a different shuffle convention. Step 3 cancels labeled mixed corners using an explicit adjacent swap with no fixed point. Only the vertex being deleted changes, so equality of the surviving generators holds even with repeated entries. Step 4 checks the interior horizontal face by counting the t vertical letters preceding the removed horizontal move: the exponent becomes t+(i+t), with parity i. Its inverse splits the i-th horizontal move, so every term is counted exactly once. Step 5 checks both horizontal endpoints, including that the final horizontal move has b inversions. These cases require a>0; when a=1 there is no interior case, and when a=0 there are no horizontal cases.

Step 6 counts the a-i horizontal moves following the removed vertical move; the combined exponent is (a-i)+(i+j)=a+j, exactly the tensor sign. Its inverse splits the j-th vertical move. Step 7 checks the initial vertical move removes a inversions and the final vertical move removes none. These require b>0, and the b=1 and b=0 cases are addressed. Step 8 partitions all labeled boundary terms into these cases, so it uses no assumption that different labeled terms evaluate to distinct generators. It deals separately with a=b=0, where the degree-zero boundary is zero. Step 9 checks the augmentation on each basis pair, under the canonical identification of the two copies of Z tensored over Z with Z. Step 10 verifies naturality entry by entry for arbitrary monotone maps, including noninjective maps; it also verifies compatibility with deletion and augmentations.

For E, I tested the actual displayed identity by a finite integer-coefficient enumeration, not by normalizing or discarding repeated vertices: all 1,156 pairs of weakly increasing strings in [2] with a,b=0,1,2,3 passed. This includes p=q=0 by taking constant strings, a=0 or b=0, a=b=1 (the two mixed paths), and a=b=0. All 25 nonrepeated generic pairs with a,b=0,...,4 passed too. These checks support the explicit general proof; they are not substituted for it. No assumption about strict monotonicity, nondegeneracy, invertibility of coefficients, or positive a,b enters the proof.

I ran LeanFinder with two phrasings, Loogle, LeanSearch, and the required Mathlib grep, and read their actual outputs. The alternating-face complex only gives the differential formula; Dold–Kan projections concern a single simplicial object; tensorHom tensors already existing chain maps. The product-simplex coordinate lemmas in `Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean:35–73` identify pair strings and deletion but contain no signed shuffle sum or its boundary identity. I read that source and `AlternatingFaceMapComplex.lean:40–120`, and checked the reported Dold–Kan projection definitions. None is an exact or one-line specialization of this item. No Mathlib leaf is claimed and no invented search is recorded.
