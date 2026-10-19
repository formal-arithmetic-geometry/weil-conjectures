## Worker report

Files written: dag/nodes/sec-zeta-weil/lem-zl-bounded-free-finite-subcomplex.json (statement, split; no exact Mathlib match), citations.json, and this report. There are no new nodes and no Mathlib leaves created. The statement and its statement dependencies are unchanged.

Attachments: none. The exact blueprint tag has no declaration in WeilConjectures/. Searching the notions located WeilConjectures/Algebra/Homology/ModuleCat/Subcomplex.lean, read throughout: CochainComplex.SubcomplexFamily.IsFinite (lines 81-85) means finitely generated terms, not finite free. Its span construction (lines 100-129) and exists_mem_range_tensor (lines 238-250) therefore do not give this item. The derived-dualizable implementation in CategoryTheory/DerivedCategory/Perfect/Dualizable.lean likewise describes a finitely generated subcomplex and a Noetherian route. It is not an attachment to this arbitrary-ring finite-free statement. No upstream master sorry was treated as a finished proof.

WANTED: none.

The item was a statement-only child of lem-zl-ring-derived-dualizable-perfect. I read the chapter sec-zeta-weil, unit sk-prop-smooth-proper-purity, and the current ancestor proof prop-zl-smooth-proper-relative-purity. The recorded ancestry supplies the ordinary-scalar dualizable/perfect input to the field-stage evaluation criterion. This split stays below that route and follows the item's own source: Stacks more-algebra.tex, Tag 0FNR, lemma-complex-bounded-above-free-colim-bounded-finite-free, lines 38552-38578. The statement agrees with that lemma, specialized to a commutative ring. No statement dispute or missing hypothesis was found.

I made the source's descending induction precise by asserting a lower support bound as part of its induction hypothesis. Without making that bound explicit, the phrase “take G equal to H above a” can hide an unnecessary gap in the splice. The proof now gives the coordinate restriction/extension isomorphism for the new term and checks each differential at the splice. No external theorem is needed for these finite-support identities.

Nothing remains unfinished in this one-level split. No Lean was written and no compiler or build was run.

## Searches and blueprint

Searched the entire DAG for Tag 0FNR and the finite-basis/support and finite-free-subcomplex notions; the tag occurs only on this item and its parent lem-zl-ring-derived-dualizable-perfect, which uses this very input and cannot be cited back. Ran blueprint_refs.py ancestor on the item and blueprint_refs.py search for “finite free subcomplex”, “bounded above free”, and “finite subcomplex”: all three searches gave zero blueprint matches. Retained the precise existing blueprint.from.place and via chain; same_as remains empty. No new definition of complexes or of freeness is introduced.

All five item searches listed in mathlib_searches were run through msearch.py and their returned declarations read, including the second LeanFinder phrasing. searches.jsonl contains their actual results. Loogle and grep returned no hits. LeanSearch returned simplicial subcomplex facts, finite-generation statements for suprema, and finite-support membership in a supremum: none supplies a subcomplex with free terms. The first LeanFinder query returned simplicial and Nobeling/ZSpan declarations with different objects; the second returned bounds predicates for complexes and injective-factorization instances. These do not supply the coordinate-subcomplex assertion. No service was unavailable, and no query was invented or added beyond the actual command log.

## Not duplicates

No new nodes. The two Tag 0FNR occurrences are the item itself and its parent, not an independent reusable finite-free-subcomplex theorem. Elementary finite-coordinate support calculations were kept in the proof instead of being made redundant nodes.

## Review by NL

I checked the six written steps against Stacks Tag 0FNR, label lemma-complex-bounded-above-free-colim-bounded-finite-free, with the source open. There are no new-node source claims to check. I also opened the statement of def-weil-abstract-derived-category, the sole proof citation, and copied its cochain-complex sentence verbatim into citations.json for step 5. In particular that sentence explicitly gives d^(r+1)d^r = 0; no property of localization, cohomology, or the derived category is borrowed from it.

Step 1 states P(t) for every finite list in degrees at least t, including the empty list, and requires vanishing below t and above b. The base t=b+1 uses the actual upper vanishing of F, so the input elements in all those degrees are zero. Ordinary natural-number induction on b+1-t applies even when the requested degrees are negative. This is the explicit version of the source's descending induction and invokes no other lemma.

Step 2 uses the meaning of free already written in the item: choose an isomorphism with a direct sum, whose coordinate functions have finite support. The union of the finitely many supports is finite. Extension by zero and coordinate restriction are the two inverse A-linear maps; this proves finite freeness of the coordinate submodule without assuming a finitely generated submodule of a free module is free. Step 3 is the same direct-sum coordinate calculation for the finitely many images of the selected coordinate vectors, with the displayed sum explaining exactly why their differentials lie in the next selected span. Both steps are elementary calculations from definitions, not uncited structure theorems.

Step 4 applies precisely P(t+1) to the enlarged finite list; all its degrees have been verified to be at least t+1. Its lower vanishing bound ensures that splicing in E at t uses no discarded nonzero lower term of H. This is an induction hypothesis within the proof, not a new node restating the desired conclusion. Step 5 checks separately n<t, n=t, and n>t. The middle case is the displayed linear combination in the c_k from step 3, and the last case uses the subcomplex supplied by the induction hypothesis. The only cited statement, def-weil-abstract-derived-category, explicitly says that the original differentials square to zero. Their restrictions square to zero by injectivity of submodule inclusion, as spelled out; no additional non-elementary fact is used.

Step 6 checks every requested element, each term's finite freeness, both support bounds, and termination of the finite induction. Enumeration of a finite index set identifies A^J with A raised to its finite cardinality. This completes the source's construction rather than moving its content into another node. All six steps are below 2000 characters and each elementary label is justified by the displayed finite-coordinate or induction calculation.

For the B-E self-check, every object in the unchanged statement is introduced there, subcomplex and free/finite-free are explicitly defined there, and the cochain notion uses its existing definition node. All TeX uses single logical backslashes. All proof uses are exactly the proof_deps union; the sole dependency is a definition, not an off-route theorem; no cyclic edge was added. There is no source theorem quoted by tag in place of a proof step. No nonsplit new node or restatement of a clause was created.

I tested the empty list; inputs only above b (all zero); negative degrees; the zero complex; a one-term free complex; the zero ring; and a two-term complex over Z/4Z with differential multiplication by 2. In the last example the span of the image 2 need not be free, but the method enlarges it to the coordinate submodule (the whole rank-one module when necessary), so it remains valid. At t=b the next ambient module is zero and the splice differential is automatically zero. Empty J and K' are permitted throughout. Commutativity is more than the source requires; no Noetherian, domain, nonzero-ring, projectivity, or lower-boundedness assumption was added. The only correction during drafting was checking the tag of the parent's dualizability lemma against the tags table: it is 0FNS, not 0FNT.

Validation: the required server dry run is run after this report is written; its result is recorded below when complete.

Server validation: deliver.py --no-push exited 0 and printed “OK (not pushed) deliver/NL/lem-zl-bounded-free-finite-subcomplex at 8e11490c34: preflight passed”. No diagnostics required a mathematical repair. The report now records that completed validation before the final dry run and push.
