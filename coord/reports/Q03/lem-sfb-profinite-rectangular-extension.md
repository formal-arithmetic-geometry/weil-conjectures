## Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-profinite-rectangular-extension.json` (statement, now split; no exact Mathlib match); `citations.json` (the two proof citations); this report. No new DAG nodes and no new Mathlib leaves. The proof reuses the existing Mathlib leaves `lem-weil-pbc-profinite-clopen-basis` and `lem-weil-pbc-tychonoff-product-quasi-compact`.
2. Attachments: none. Searches of `lean/WeilConjectures/` by the blueprint id, rectangular extension, closed extension, clopen extension, and profinite/locally-constant terminology found no project declaration with all clauses. The additional search of `lean/Sheaf/` found no exact statement either. No compilation was run.
3. WANTED: none.
4. The item was statement-only; its statement is correct and was preserved verbatim. Its existing searches and metadata were retained. The new argument supplies the rectangular-neighbourhood and atom-refinement construction, including why the extension has the requested common coordinate partition. No mathematical error or route change was found. `blueprint_refs.py ancestor` returns None, consistent with the inherited null ancestor; the descriptive place and via chain remain intact. Whole-blueprint searches for clopen, rectangular, and closed subset found no equivalent blueprint assertion, so `same_as` remains empty.
5. Unfinished: no mathematical work remains on this one-level split; independent maintainer review follows delivery.

## Sources and searches

Read `literature/stacks-project/topology.tex`: Tag 08ZY, `lemma-profinite`, constructs finite clopen partition quotients; Tag 08ZZ, `lemma-profinite-refine-open-covering`, provides finite clopen refinements and the underlying clopen-neighbourhood description; Tag 08ZU, `theorem-tychonov`, states product quasi-compactness. The rectangular extension is an agent-written consequence, not attributed as a verbatim theorem of these tags. Read the chapter/unit records, the current main-20261015 unit text, and paragraph (3) of `sk-thm-sf-ctf-stability-direct-images.proof.md`: this remains the auxiliary profinite input below the delegated open direct-image theorem. No SGA source is used.

Before considering any new fact, searched all DAG nodes by 08ZY/08ZZ, clopen basis, compact products, rectangular and extension terminology, and ran the whole-blueprint searches. These located the two existing leaves, so no new basis, compactness, Boolean-atom, or extension node was made. Boolean atoms and the continuity verification are elementary steps, not renamed clauses passed to a new node.

All new Mathlib searches ran through `msearch.py` and their actual records are in `searches.jsonl` and appended to the item's `mathlib_searches`. Both semantic phrasings, Loogle, LeanSearch, and source grep were available. Read the candidates in `Topology/Category/Profinite/Nobeling/Span.lean:228`, `Topology/Category/Profinite/CofilteredLimit.lean:124`, and `Topology/Separation/Profinite.lean:147`: they concern Boolean-coordinate integer functions, factorization through an already supplied limit, or separation of finitely many closed sets by clopens. None states the required extension together with one partition of T in all coordinates. The basis statement itself was checked in `Topology/Separation/Profinite.lean:43–79`; it is already represented by the existing leaf.

## Not duplicates

No new nodes. The existing basis lemma supplies small clopen neighbourhoods; the existing product lemma supplies compactness. Neither asserts this item's extension or its common coordinate partition.

## Review by Q03

I read the item, the statements of both cited leaves, and the three Stacks places listed above against delivery-errors B–E. The item introduces every space, topology, function, and partition, and its size convention is its existing statement dependency. There are no new statement-only nodes whose sources or notion dependencies require review. The two quotations in citations.json are copied from the cited nodes' statements, rather than their proofs or definitions.

Step 1 handles empty T using k>=1, and empty K using the nonempty block T. Neither requires a theorem beyond the stated meanings. Step 2 uses exactly the pointwise clause of `lem-weil-pbc-profinite-clopen-basis` on T, whose compactness, Hausdorffness, and total disconnectedness are explicit hypotheses. Discreteness of M makes a singleton fibre open; the definition of subspace topology and the finite product basis give the ambient rectangle. No claim about extension is borrowed from the basis lemma.

Step 3 uses exactly the product compactness asserted by `lem-weil-pbc-tychonoff-product-quasi-compact`, with the finite index set of k coordinates and every factor T compact. Closedness of K is used precisely to add its open complement to the rectangle cover. Taking a finite subcover then covers K by finitely many of the rectangles. This writes out the closed-subspace compactness argument, so there is no uncited closed-compactness lemma.

Step 4 explicitly constructs every Boolean atom and proves finiteness, clopenness, covering, and disjointness from membership patterns. Step 5 checks the crucial rectangular refinement: if a cell meets a selected rectangle at y, each coordinate atom is contained in the corresponding coordinate clopen. Consequently every cell meeting K has a unique c-value on its intersection with K. The rectangles themselves need not be disjoint; the proof never assumes they are.

Step 6 defines h from those unique cell values and sets it to zero on precisely the cells missing K. This verifies both extension and the extra zero clause. Step 7 proves continuity directly by writing every inverse image as a union of open cells. These steps contain only the displayed finite-set and inverse-image arguments; they hide no auxiliary non-elementary comparison. Both non-elementary steps cite existing Mathlib leaves, which are permitted tools across units. No proof step exceeds 2000 characters; the whole assembly is under 3000 characters.

I checked k=1, a one-point T, finite discrete T with K proper, K=T^k, empty T, empty K, and M=0. For a finite discrete example the singleton partition is available and cells outside K receive zero. The proof also works for arbitrary discrete pointed coefficient sets, so it uses no accidental cancellation or nonzero-element assumption. I corrected no statement. The substantive addition was the explicit finite atom argument and the containment proof that makes the values well-defined. This is the direct-delivery self-review required by the brief, with independent maintainer reading still to come.


## Repair of the returned landing

The sole return was L's refusal to land a side completion that was absent from the live DAG read by the queue. The retained delivery receipt identified head `e27e36f5d80`. I continued its seven-step proof, report, citations, and search log. The required first dry run exited successfully at `4ac76f14d8f`; it did not push. I then rebuilt the sandbox item from the current shared DAG node, applying only the retained split-owned fields, and clarified step 3 rather than sending an unchanged re-push.

The current shared item is `unsplit`, with empty proof and proof dependencies. Its statement, source, size-convention statement dependency, chapter, unit, creation record, and blueprint provenance agree with the retained version. The difference to be delivered is the actual split, its Mathlib searches and split report. No released repair note exists for this id. Delivery is rebuilt on the tool's current base, not on the old delivery branch.

I reread the complete current files of `lem-weil-pbc-profinite-clopen-basis` and `lem-weil-pbc-tychonoff-product-quasi-compact`. Their statements still contain the two retained citation quotes verbatim: the first gives exactly the clopen neighbourhood in step 2, with compact Hausdorff totally disconnected hypotheses; the second gives exactly compactness of the finite product in step 3. Both are still Mathlib leaves, so no additional route approval is needed. No cited statement change requires changing a hypothesis, dependency, or citation. I also reopened Stacks `lemma-profinite`, `lemma-profinite-refine-open-covering`, and `theorem-tychonov`, and the main-20261015 unit's direct-image proof paragraph (3). The auxiliary construction still serves the same delegated open-coefficient branch.

Step 3 now explicitly removes the open complement of K from a finite subcover and explains why the remaining rectangles still cover K. Because this branch assumes K nonempty, at least one rectangle remains. Steps 1 and 4–7 retain the empty-case treatment, the finite Boolean membership-pattern partition, the containment proof for a cell meeting K, and the direct inverse-image proof of continuity. All seven steps are shorter than 2000 characters. The statement still includes empty T, empty K, and M=0 without extra hypotheses. There are no new nodes or leaves. The prior recorded Mathlib query results were reread and retained; the statement and search question did not change, so none was invented or repeated.

Current cited-node file fingerprints read for this repair:

- `lem-weil-pbc-profinite-clopen-basis`: SHA-256 `393d7747c1a2f2d727035049e2d31d9eb731a180392e8b0ebaf6b5fac3f47cce`.

- `lem-weil-pbc-tychonoff-product-quasi-compact`: SHA-256 `92a4a2cc15394d3610ff16ca29d058944e453ead6ab741882de8f52a740f3842`.


## Repair retry 2026-10-23

I continued the retained sandbox rather than restarting the split. The mandatory initial dry run completed successfully, without pushing, at `05b68cedbf5`. It checked the retained delivery against the current server base. I then reconstructed the sandbox item from the current shared DAG record and overlaid only the retained split fields. The current base still has this item unsplit; its statement, source, statement dependency and provenance are unchanged. No released repair note exists. The earlier returned head and prior repair receipts remain documented above.

I reread both cited nodes in full. Their statements and fingerprints still agree with the retained citation evidence, so neither citation needed replacement: step 2 uses the pointwise clopen-basis assertion with the hypotheses supplied by T, and step 3 uses product quasi-compactness with every factor T. I also reread the size convention, Stacks Tags 08ZY, 08ZZ and 08ZU, the main-20261015 unit and its direct-image paragraph (3). The current auxiliary route agrees with that delegated open-direct-image branch. No SGA source is involved.

For a concrete improvement to the retained argument, step 4 now bounds the number of Boolean atoms by the number of membership patterns and explains explicitly that the generating family combines all coordinate clopens, giving the same partition in every coordinate. Step 5 now explicitly checks that different selected rectangles cannot assign different values to a cell meeting K. Steps 1, 6 and 7 still verify the empty cases, zero assignment outside K, extension and continuity directly. These are finite set and inverse-image arguments, with no hidden lemma and no step over 2000 characters; the total proof remains under 3000 characters. I checked the one-point space, k=1, K empty, T empty, K the whole power, and the zero coefficient group again.

I read all retained search-log results and the candidate declarations in the pinned Mathlib source. The search question and statement have not changed, so the existing searches are reused. Fresh project-source searches again found no declaration giving every clause. Blueprint searches for rectangular and clopen again found no equivalent imported assertion. This retry adds no DAG nodes and no Mathlib leaves. Both citation quotes were checked verbatim against the current statements. This is a repair on the current base with explicit argument clarification, not an unchanged re-push; the final dry run and direct push use the authorized delivery tool.
