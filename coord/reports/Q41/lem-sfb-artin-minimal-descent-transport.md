# Stage-1 report: lem-sfb-artin-minimal-descent-transport

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-artin-minimal-descent-transport.json`: statement, split; no Mathlib match. The statement and its existing source are unchanged. Eight proof steps replace the empty proof.
- `citations.json`: one verbatim statement excerpt for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's own record.

New nodes: 0. New Mathlib leaves: 0. The sandbox initially had no node or report; the item was copied from the current read-only repository. No Lean, compiler, Lake, repository write, or direct git operation was used.

## Attachments

None. I searched `lean/WeilConjectures` for the exact item id and the concepts Schlessinger, cofibered/cofibred, minimal subring and smallest descent. No declaration states the item. The existing Mathlib searches in the imported item were retained and read. The five fresh searches recorded by msearch.py are the two phrasings via LeanFinder, the LeanSearch query, Loogle `"Schlessinger"`, and the grep recorded in searches.jsonl. All services answered. Their hits concern Artinian ring images and finite length, formal smoothness, minimal prime ideals, or subring closure, not the groupoid-valued assertion. The algebraic hits do not provide an attachment for this item.

## WANTED

None. The proof and all prerequisite sources are available locally.

## What was wrong or missing

The imported item had no proof. The Stacks statement itself is sound; no STATEMENT-DISPUTED correction is needed. I made the finite-length minimality argument explicit, checked that image rings remain in the marked test category, and gave the composition-constraint formula for the image functor. In particular, the proof does not pretend that an arbitrary pullback along two inclusions is an Artinian test algebra: both applications of (S1) have a specified surjective leg.

The inherited blueprint ancestry has `from.node = null`; the required ancestor command reports None as well. I retain that existing metadata and its full nonempty place and via chain. The current blueprint at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, proof (3), keeps the direct-image preservation route. This item remains the Tag 06T1 supporting input for the already supplied minimal-versal descent node (06T2); I did not change the unit or chapter route.

## Not duplicates

No new nodes. I searched the whole DAG for 06T1, lemma-smallest-where-descends, Artinian subring images and finite-length arguments, and searched the whole imported blueprint using blueprint_refs.py for 06T1, 06GG, minimal subring, ring of definition, smallest where descends, Artinian rings of definition and minimal objects. The 06T2 node `lem-sfb-versal-minimal-subring-descent` is a downstream user, not a substitute: it concerns a versal formal object over a complete ring. The bounded-cotangent and power-series nodes mentioning 06T1 use the Artinian statement or cite its source but do not state this lemma. Existing generic length and test-ring lemmas suffice, so I created no specialized duplicate.

## Review by Q41

I read formal-defos.tex at the paragraph defining S_x and f_* immediately before Tag 06T1, both clauses and their proofs, the finite-length discussion and Tag 06GG, the definition of the marked Artinian category, and the surrounding fibre-product discussion. I also read algebra.tex at Tags 00DV (Nakayama), 00JB (Artinian self-length) and 02M0 (restriction of length). There are no new-node sources to audit. I opened every cited DAG node and compared its statement with the exact use, rather than using anything hidden in its proof.

Step 1 uses the stated Nakayama lemma with I the unique maximal ideal of Lambda and M=l. Finiteness of M is an item hypothesis. If an element of I has nonzero image in l, its invertibility makes IM=M; Nakayama then contradicts the nonzero field. This verifies the contraction and finite residue degree required in step 2, including the nonclassical case where l is a proper finite extension of Lambda/m.

Step 2 uses the definition node for the local marked tests, Artinian self-length for A as its own module, and `lem-exc-semilocal-restriction-length` for finite length after restriction. Its hypotheses really hold: Lambda is local, the set of maximal ideals of A is a singleton, its contraction is Lambda's maximal ideal by step 1, and its residue degree is finite. Only the finite-length conclusion is used; no localization comparison is assumed. This generic off-unit algebra input is declared in split_report.tool_uses. The self-length and Nakayama nodes are already Mathlib leaves.

Step 3 uses the chain definition of length and the groupoid fibres from the test-category definition. Choosing least length among objects mapping to the specified object gives minimality below that object; it does not assert a unique smallest subring. The strict length inequality follows by appending the larger submodule to a maximal finite chain. Equal underlying rings make the arrow an isomorphism in the fibre, with its inverse still over x.

Step 4 uses the nilpotence clause actually stated in `lem-sfb-artin-local-test-algebra`, plus the definition of a test algebra. I wrote the quotient/image argument: the marked residue map has nilpotent kernel, inverses lift by a finite geometric series, and descending ideal chains pull back under a surjection. This is an elementary calculation, not a new theorem to outsource. Both image maps are local and residue preserving.

Step 5 uses only the transport functors, natural composition constraints and their associativity from the definition node. The formula has domain j_*q_*y' and codomain x; c_{j,q} is followed by c_{f,i}^{-1}, then f_*beta and gamma. This proves the square over u commutes, and naturality and associativity give the induced commuting triangles for arrows. I checked the identity case and composition directions.

Step 6 uses the pullback clause of the test-ring node with A_1=A'', A=C and A_2=B'. The leg B'->C is onto by construction. Its first projection is injective because A''->C is an inclusion, so the lifted object really belongs to S_y. Minimality forces this preimage to equal B', and surjectivity gives A''=C. (S1) is an explicit item hypothesis, not borrowed from (RS) or from a definition.

Step 7 again uses the pullback clause, now with A_1=A', A=A and A_2=B and the assumed surjective f. Projection to B is injective and projection to A' is onto; the compatible lift from (S1) has image ring A' and gives the required isomorphism over x. Step 8 uses the earlier minimal-object construction and functoriality. Minimality of the specified target x' forces equality of subrings, hence an isomorphism over x, and the composite of the (S1) arrows supplies the final commuting square and surjectivity B_0->A'.

I checked B--E of delivery-errors: self-contained unchanged statement, verbatim citations for all uses, no use of another node's proof, no new elementary/duplicate/clause nodes, no hidden general lemma in a long step, and no SGA route. Every step is under 2000 characters. Small cases: for Lambda=l and F the terminal groupoid, the embedded field l is the minimal test subring; for a proper finite extension l/(Lambda/m), A=l has no proper test subring with the required residue marking; identity f gives the identity transport; a non-surjective inclusion is allowed in clause (1) without invoking clause (2); the surjection l[epsilon]->l and the pullbacks with A'=A and with B'=B have the asserted injective/surjective projections. No uniqueness of minimal models, equality of independently chosen transports, or descent over a non-test subring is used.

## Unfinished

Nothing in the requested stage-1 split. All new-node, source, citation and route checks are accounted for; the required dry run and direct delivery follow.
