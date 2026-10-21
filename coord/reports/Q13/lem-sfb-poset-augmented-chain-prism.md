## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-poset-augmented-chain-prism.json`: statement item, now split into eight explicit elementary basis calculations; Mathlib verdict: no exact or one-line match.
- `citations.json`: both step citations, with verbatim excerpts of the definition's statement.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searching the current project under `lean/WeilConjectures/` for the exact blueprint tag, prism, strict chains, posets and order complexes found no declaration stating the item. The inherited item has no Lean attachment or `lean_audit` entry.

WANTED: none. The exact reference needed for the sign calculation is available in `literature/stacks-project/simplicial.tex`, Tag 019S, `lemma-homotopy-s-N`, especially `equation-homotopy-to-homotopy`, lines 4739–4846. The augmented strict-chain version is an agent adaptation, and `proof_origin.by` is therefore `agent`.

The item statement is correct and unchanged. The original node had no proof. Its source already warned that normalization and augmentation were extra obligations: these are now proved explicitly, rather than attributed to Tag 019S. Stacks uses the opposite signed homotopy convention in its displayed formula, so the boundary signs were calculated directly to get precisely `g_* - f_*` for the item's formula.

The inherited `blueprint.from.node` is null, and `tools/blueprint_refs.py ancestor` reports None. I retained that maintainer-owned provenance rather than manufacturing a blueprint ancestor. The current blueprint direct-images proof, paragraph (3), gives the open-direct-image route but does not assert the combinatorial prism lemma. This item supplies the contraction argument in its parent `lem-sfb-product-chain-proper-interval-homology`. No unit or chapter field was changed; this is not the unit's key node, so no realization fields were written.

Nothing remains unfinished within this split. No Lean was written and no compiler, Lake, build, or local preflight/check script was run.

## Searches and existing statements

Read the entire item, its parent, chapter `sec-six-functors-basics`, unit `sk-thm-sf-ctf-stability`, current direct-images proof, and the two potentially relevant existing nodes `lem-weil-pbc-simplicial-homotopy-free-chain-homotopy` and `lem-sfb-split-simplicial-nondegenerate-homotopy`. Searched the whole DAG for 019S, prism, weakly increasing tuples, degenerate subcomplexes, normalized chains and simplicial homotopies; blueprint searches for prism and poset give no equivalent imported statement.

The existing free-chain homotopy node gives existence on unnormalized nonaugmented simplicial chains, not the displayed normalized augmented operator. The split-simplicial node gives a homotopy equivalence with a nondegenerate complex, not the specified maps or formula. Neither statement was used as a black box. Creating a node for a quotient-by-repetitions calculation or for one prism clause would merely duplicate elementary steps or move the item's clauses elsewhere.

All new Mathlib searches were run through the prescribed `msearch.py` command and recorded verbatim, retaining the inherited search history. The results are in `searches.jsonl`. The second semantic phrasing and targeted grep were also run. Read `DoldKan/Homotopies.lean` lines 94–110 and `DoldKan/HomotopyEquivalence.lean` lines 48–76: these concern normalization projections of one simplicial object. Read `SimplicialSet/Homology/HomotopyInvariance.lean` lines 98–116 and `Nondegenerate.lean` lines 30–90: general simplicial homotopy and normalization exist, but comparing the poset chains, descending the displayed operator, and adding degree minus one are genuine extra work. The item is not a one-line specialization. LeanSearch returned general Homotopy and OrderHom declarations; the valid comma-separated Loogle query and broad grep found no match. Every new service query succeeded; no downtime was represented as absence.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to distinguish.

## Review by Q13

I read Stacks Tag 019S and its preceding signed calculation against all eight proof steps. I also read the statement of `def-weil-pbc-module-chain-complex-homology` in full. It defines both integer-indexed complexes and their chain-map commutation equation, exactly the two statements quoted in `citations.json`. No step takes any result from a cited node's proof.

Step 1 cites that definition solely for what a complex means; it proves the square-zero condition by matching both orders of two deletions, separately handling the augmentation. It requires neither a nonempty poset nor a field. Step 2 has no cited theorem: for one fixed adjacent equality, the two deletion terms cancel, and all others remain repeated. The quotient has exactly the strict tuples as a basis because it kills a subset of a free basis; its inverse is described on those surviving generators. This is a short direct calculation, not an invocation of a general normalization theorem.

Step 3 again cites the definition, now for the chain-map equation. Monotonicity supplies a valid weak tuple and equality preservation supplies preservation of repeated generators. The proof checks degree zero explicitly. Step 4 checks identity and composition on the actual generators, including the empty chain, and accounts for a collapse remaining a collapse under composition. It uses no external result.

Step 5 checks every junction inequality using the two actual hypotheses: monotonicity and pointwise `f <= g`. The adjacent repeated input pair always survives in either the f block or the g block; the two cases cover every prism index, including the junction. Thus descent does not rely on an unproved identification of normalized complexes. Step 6 lists both families of off-junction faces, their partner indices, and the opposite signs. Its converse enumeration shows every term of `Hd` is matched exactly once. Step 7 computes both junction faces and telescopes the resulting finite sum, with the correct orientation `g - f`; quotienting uses the explicit maps already constructed in steps 2, 3 and 5. These are coefficient identities on free bases, with no hidden comparison lemma or other non-elementary premise.

Step 8 handles n = 0 and n = -1 separately and explains the vacuous lower degrees and empty-poset cases. When f = g each prism tuple itself repeats the junction vertex, so h is zero, consistent with the identity. No signs are divided by anything, so the calculation also applies in characteristic two and over the zero ring. Finiteness is retained as stated, though none of these finite sums require more than a finite tuple.

I checked delivery-errors B–E: no new statement-only nodes were needed; the item introduces every object and its conventions; TeX has single escapes in the decoded strings; the Stacks tag/label were verified in the local tag table; citations are verbatim statement excerpts; no proof depends on a descendant or an off-route theorem; there is no assertion of a hidden standard result; and all eight steps are below 2000 characters (maximum 805). The elementary flags reflect that each is an explicit basis formula, cancellation or generator check, rather than a theorem being hidden under that flag. The report distinguishes the available source's assertion from the extra normalization and augmentation work.

For small-case verification I ran `check_small_cases.py` in this sandbox, using integer coefficients. It enumerated 51 posets with a chosen linear extension through size four, all domain posets through size three, 41,851 comparable pairs of monotone maps, and checked 199,678 augmented strict-chain prism identities. It also checked d squared and chain-map commutation, including empty chains and collapsed images. Every check passed. This finite computation supports the written arbitrary-degree cancellation argument; it does not replace it.

The server-only `srvcheck.py ... review_split` passed with zero new nodes. It notes that the inherited unit has no realization recorded; that unit-level work is outside this item's scope.
