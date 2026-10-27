## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adequate-locally-separated-universality.json: item split in five steps; original statement retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-adequate-geometric-fibres-submersion.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-stein-submersive-reduced-descent.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-locally-separated-closure-equivalent-images.json: statement, unsplit, no Mathlib match.
- citations.json: full verbatim statement quotes for each step/node citation.
- searches.jsonl and search-results.json: actual msearch log and full results. The item and each new node received LeanFinder, LeanSearch, Loogle and Mathlib grep searches. Both natural-language services ran successfully and gave different phrasings. No leaf was inferred from a similarly named scheme theorem.

## Attachments

None. Searched the live WeilConjectures source both for the blueprint id and for adequate-moduli/closure/descent concepts; no project declaration states this item. The pre-existing Mathlib leaf lem-weil-pbc-diagonal-immersion is reused, not recreated or claimed as a project attachment.

## Wanted literature

WANTED: Alper, Adequate moduli spaces and geometrically reductive group schemes, arXiv:1005.2398v3, Theorem 5.3.1 and Proposition 7.1.1/Theorem 7.2.1, for this item and its three new nodes. Read online at https://arxiv.org/pdf/1005.2398v3; no local PDF was present and no literature file was written.

WANTED: Rydh, Submersions and effective descent of etale morphisms, Proposition 7.2, §7.3 and Theorem 7.4, for lem-sfb-stein-submersive-reduced-descent. Read the author's PDF https://davidrydh.se/papers/submersion20100305.pdf, printed pp.28--29. No local PDF was present. The online source has the necessary weak-normality hypothesis: the new node uses the stronger structure-sheaf isomorphism as in Alper's proof, not bare universal submersiveness. The item has proof_origin.by = agent because the local literature is missing and the source's reduced-diagonal argument has been expanded.

## Problems found

The item was an unsplit source citation. Its two stated cases are correct, including arbitrary nonseparated schemes, and no statement correction is made. Its title mentions separated targets, but the quantifier over schemes does not require separatedness; step 5 preserves this.

The imported created.item ancestry stops at lem-sfb-admissible-direct-image: its creator is a module name rather than a node id. tools/blueprint_refs.py ancestor therefore returns None for this item. The existing descriptive blueprint.from.place correctly names det-thm-sf-ctf-stability-direct-images proof (3). New nodes retain the computed null ancestor and the via chain and expand that descriptive place; no upstream metadata is edited. This is an inherited metadata defect, not a replacement route or an invented blueprint ancestor.

The source's reference to Rydh is not itself a complete statement of descent for stacks. That substantive stack/Stein descent input is exposed as an unsplit lemma; it is not called elementary. In particular the proof does not assert effective descent from universal submersiveness alone. No SGA source is used.

## Not duplicates

lem-sfb-adequate-geometric-fibres-submersion vs lem-sfb-power-lifting-quotient-submersive: the existing node is only for affine quotients by an affine finite-type group with a global power-lifting hypothesis; the new node applies to every adequate moduli space and includes its geometric closure-fibre criterion.

lem-sfb-adequate-geometric-fibres-submersion vs lem-sfb-affine-pgl-quotient-orbit-topology: the existing node is specific to finite-type affine PGL actions and includes invariant-ring finiteness and closed orbit information; the new node has neither an action nor a finite-type hypothesis and concerns the stack topology.

lem-sfb-stein-submersive-reduced-descent vs lem-sfb-adequate-locally-separated-universality: the new node assumes no adequacy or geometric fibre equivalence and only descends maps satisfying a reduced-relation equalizer condition. The item still has to prove that condition, including the diagonal argument. Thus it does not restate universality or either clause of the item.

lem-sfb-locally-separated-closure-equivalent-images vs lem-sfb-adequate-locally-separated-universality: the new node only identifies two geometric images, with no quotient, factorization, uniqueness or map Y to T. It is the geometric-points sublemma behind the source's assertion that W is surjective.

Whole-DAG statement searches for universal submersiveness, closure equivalence, immersive diagonals and weakly normal descent found no other matching statement. Whole-blueprint searches for adequate, submersive, weakly normal, closure equivalent and reduced descent found none; geometric fibres gave general scheme/cohomology items, not this assertion. The scheme-diagonal fact already exists as lem-weil-pbc-diagonal-immersion (Stacks 01KJ) and is cited. No new node carries a Stacks tag of an existing node.

## Review by Q70

I read Alper v3 Theorem 7.2.1, printed pp.36--37, and its Proposition 7.1.1, printed pp.35--36, together with Theorem 5.3.1(3),(5), printed pp.29--30. The new geometric-fibre node records precisely those two parts of 5.3.1. For the descent node I read the exact Hom diagram in Alper and Rydh Proposition 7.2, §7.3 and Theorem 7.4: Rydh requires a quasi-compact quasi-separated weakly normal universally submersive map, and his theorem itself is stated for algebraic spaces. The new stack statement is the general descent input of Alper's proof, with the stronger O-isomorphism and stack extension explicit, left unsplit for its own future proof. It is not marked a Mathlib match. The images node isolates the closure-equivalence argument used for surjectivity of W, and contains no adequacy hypothesis or conclusion of universality.

Step 1 cites the full general geometric-fibre statement, the actual adequate-moduli definition and the actual descent statement. The definition explicitly supplies qcqs and O_Y = phi_*O_X, not any vanishing or exactness theorem. The geometric node supplies universal submersiveness and closure intersection over each algebraically closed extension. All hypotheses of the descent statement are thereby in force.

Step 2 cites exactly the geometric-fibre node for closure intersection of the two objects over the same Y(Omega), and exactly the images node for equality in T(Omega). Equality of underlying topological images alone would not justify the diagonal pullback, so that weaker assertion is deliberately avoided.

Step 3 has no black box: W is the actual pullback of the immersive diagonal, so pulling back the local closed/open factorization gives an immersion. On a reduced smooth chart its surjective open part is the whole chart. An ideal defining a closed subscheme with full support is contained in every prime, and reducedness kills it. This proves W = R and hence equality of the two morphisms by the fibre-product universal property. This is the short elementary reduced-ring argument, not an uncited general descent or algebraization theorem. Reduction and smooth-chart testing were included in the descent node's setting.

Step 4 uses the descent node's statement, not its proof: it explicitly supplies both injectivity and the image condition hp1 = hp2. Those give existence and uniqueness. Step 5 uses the existing node lem-weil-pbc-diagonal-immersion, whose statement says the diagonal of every scheme morphism is an immersion. I opened this node and Stacks schemes.tex, lemma-diagonal-immersion (Tag 01KJ), and checked that applying it to T -> Spec k needs no separatedness or finite-type hypothesis. The algebraic-space case is the elementary inclusion of closed immersions among immersions. No general representability or descent theorem is smuggled into that specialization.

For the Mathlib hits I checked that ext_of_isDominant_of_isSeparated at Morphisms/Separated.lean:295 requires a reduced scheme and a separated scheme target; it cannot supply stack descent or the locally separated statement. Abstract RegularEpi.desc' assumes a regular epimorphism that has not been established here. Normalization and topological Inseparable/closure lemmas also do not state any new node. All search records come verbatim from the actual calls, and none of the services was unavailable. The new nodes remain statement-only, with empty proof/proof_deps and null proof_origin.

Small cases checked: identity adequate morphisms, the empty stack and target, an affine scheme quotient with nilpotents, and nonreduced Y do not require a reducedness hypothesis on X or Y. Reduction is used only on R. The diagonal argument would fail on nonreduced R: a nonzero nilpotent ideal has full vanishing locus; the explicit reduction is essential. A scheme with doubled origin is permitted since its diagonal is immersive; no separation condition was added to the scheme clause. The bug-eyed non-locally-separated space of Alper Remark 7.1.3 is excluded by the diagonal hypothesis. The general descent lemma is not asserted for arbitrary non-locally-separated targets. Constant h and X=Y have tautological compatibility on R and descend as expected.

I checked B--E of delivery-errors.md: complete object binders and inline meanings; unchanged item statement; existing-node and blueprint searches before new-node writes; three smaller lemmas rather than a renamed universality clause; no hidden non-elementary lemma in a long step (all steps are under 700 characters); union of uses equals proof_deps; no backwards dependency to the item; and full verbatim citation quotes. The only off-unit statement is the existing scheme-diagonal Mathlib leaf, declared as a generic tool in split_report.

## Unfinished work

No step of the item is left open. The three new lemmas are intentionally unsplit stage-1 queue items, as required for a split by one level. Their full statements and sources determine the next work. No Lean file, compile or build was run, and no repository or launcher file was written.


## Repair of L return (2026-10-22)

The return identifies the retained delivery as 17140e7da2a and says that its independently approved split was not promoted to the live DAG. I compared that retained sandbox version with the current shared item at 14d609e5fe8dea3b1ad2a98bd3ca3fb97666a0d8. The live item is unsplit with empty proof and proof_deps, while its statement, statement dependencies, source, created record and blueprint ancestry agree with the returned version. There is no released stage-1 repair note. I reconstructed the sandbox item from this current record and overlaid the retained stage-1 fields; deliver.py builds the delivery on its freshly fetched current origin/sheaf-dag. This is a repair delivery for promotion, not a claim that the previous side completion had landed.

I re-read every existing cited statement: def-sfb-adequate-moduli-space still explicitly includes quasi-compactness, quasi-separatedness and the structure-sheaf isomorphism used in step 1; lem-weil-pbc-diagonal-immersion still quantifies over every scheme morphism, as step 5 needs. Their full retained citation quotes remain verbatim in the current statements, so neither requires a replacement dependency or a changed hypothesis. I also re-read def-weil-field and def-trf-algebraic-space for all statement dependencies and found no incompatibility. The three supporting nodes remain absent from the shared DAG, and the current whole-blueprint adequate, weakly normal and closure equivalent searches still find no replacement. I preserved all their original statements, citations and actual search logs, and read the retained full search results rather than issuing duplicate Mathlib requests.

For the split adjustment, I tightened step 3 to work on open neighbourhoods of each reduced smooth chart where the immersion is closed. On every such neighbourhood, surjectivity makes its defining ideal lie in all primes, and reducedness kills it. The local isomorphisms imply the isomorphism on the chart and hence on R. This avoids reading the earlier phrase “its open part contains every point” as an assumption of one global factorization. Steps 1, 2, 4 and 5 keep the approved argument and hypotheses. The item statement is unchanged. I re-opened Alper Theorem 5.3.1(3),(5), Proposition 7.1.1 and Theorem 7.2.1, and Rydh §7.3/Theorem 7.4: universal submersiveness alone is still not used as a descent theorem; the structure-sheaf condition remains explicit in the separate descent node.

I checked every step/node quote against the current node statement, the exact coverage of citations.json against the five uses lists, and the proof_deps union. All non-elementary steps cite the statements they use; the elementary step 3 writes out the local nilradical argument. The empty case has no points to check; for a nonreduced chart the nilradical conclusion would fail, so reducedness is used only after forming R. All steps remain below 2000 characters. The initial required dry run passed at 392a83ef2bc before this adjustment; a fresh dry run is required for this repaired version before pushing.


## Resumed repair verification (2026-10-22)

The interrupted dry run completed successfully at 27293fb139b, with no push. I re-read the shared item and all four existing statement dependencies/citations and rebuilt the sandbox item from the current shared record, preserving only the retained stage-1 fields. The shared statement, source, statement dependencies, chapter/unit and created/blueprint metadata still agree with the retained version. The three new nodes are still absent from the shared DAG. No hypotheses or citations needed replacement.

I re-opened Alper arXiv:1005.2398v3 Theorem 5.3.1(3),(5), Proposition 7.1.1 and Theorem 7.2.1 directly from the PDF: its exact Hom diagram is the retained descent input, its diagonal pullback is the argument in step 3, and its locally separated branch supplies the two stated target cases. The previous Rydh reading and its explicit stronger structure-sheaf hypothesis are retained; a new retrieval of the author PDF returned HTTP 403, which does not alter the prior reading or the node. I read the saved Mathlib service results and logs; flat scheme descent, separated-scheme extensionality and abstract regular-epimorphism descent still do not specialize to these stack statements. The current project-source search found no adequate-moduli declaration or blueprint-tag attachment.

The additional correction is typographical: the retained proof-step strings had doubled TeX backslashes after JSON decoding. I normalized them to single backslashes in proof text only, leaving statements, source quotes and recorded search results untouched. I checked each citation against the current statement and the exact step uses, and the union of uses against proof_deps. This repair preserves the approved mathematical route and the clarified reduced-chart argument; another dry run and push follow this final file change.


## Current-DAG promotion repair (2026-10-23)

The required first dry run of the retained delivery exited successfully at ab0c65b19c4 without pushing. I then compared the retained returned version against the current shared DAG record. The live item is still unsplit with empty proof and proof dependencies. Its statement, statement dependencies, source, created record, chapter, unit and blueprint fields agree with the retained version. I rebuilt the sandbox item from that current record and overlaid only the stage-1 fields. The live file SHA-256 at comparison was 27f1697f8c57800607fb17f55905161a64043d7803b764c8541e8390fe2a4444; deliver.py performs the actual rebase onto the current server branch in its temporary worktree. This explicitly resubmits the side completion for promotion rather than assuming it is already live.

All current existing cited statements were re-read. The adequate-moduli definition still supplies quasi-compactness, quasi-separatedness and the structure-sheaf isomorphism used in step 1. The diagonal leaf still covers every scheme morphism in step 5, including nonseparated schemes. The field and algebraic-space statement dependencies retain the meanings used throughout. No cited statement requires a change of hypothesis or replacement citation. The following hashes record exactly which current statements were checked:

- def-sfb-adequate-moduli-space: 732095c4f25c19ffd71c52fcfa0dcd59b8d814181015d0f98f36189f323cefd6
- def-trf-algebraic-space: 4dd6e0b9a70e38fd0df26f6335e1720ba8d8f373598cdf09e4d236556f580f3f
- def-weil-field: 09d510cc2aa76bc1714348460bc87c06080edc245442997ce2d7ea2576b208da
- lem-weil-pbc-diagonal-immersion: c2776c8870efb5d66151cb6e51b161a96353c62df6d28dec67e0b0e208543fbb

I re-read Alper v3 Theorem 5.3.1(3),(5), Proposition 7.1.1 and Theorem 7.2.1, and retrieved Rydh Proposition 7.2, section 7.3 and Theorem 7.4 successfully in this retry. The Rydh theorem requires weak normality, so the separate descent input retains the stronger structure-sheaf isomorphism and its stack formulation, as exposed in Alper's exact Hom diagram. The descent input remains a separate unsplit node; it is not inferred from universal submersiveness alone. I read the retained search results and actual search log; no changed statement or search question required another Mathlib request. Project-source searches again found no attachment. Whole-DAG and blueprint adequate-moduli searches found no replacement for the three new inputs, which remain absent from the current shared DAG.

For steps 1 and 4, the quoted descent statement explicitly supplies injectivity and the reduced-relation image criterion; step 1 also cites the actual adequate-moduli definition and the geometric-fibre theorem. Step 2 uses the geometric-fibre theorem for intersecting closures and the images statement for equality as geometric morphisms. I adjusted step 3 to explain base change directly: pull back the open subspace and defining ideal in the diagonal's local closed/open factorization. The subsequent local nilradical argument uses reduced charts, not reducedness of the original stack or base. It proves an isomorphism of the actual fibre product, not a factorization from set-theoretic image containment. Step 5 uses the current scheme-diagonal leaf and the defining inclusion of closed immersions among immersions. All seven step/node citation entries remain verbatim in the current statements, and their pairs are exactly the proof uses. All five steps are below 2000 characters.

I checked B--E against these files and sources again: the three new nodes remain self-contained statements without proofs, have actual logged searches and precise source places, and are neither elementary assembly facts nor universality clauses. Empty objects, identity morphisms, nonreduced bases and a nonseparated scheme target still satisfy the asserted hypotheses. Reduction is essential to kill the defining ideal in step 3; no false factorization through a closed subscheme is inferred from its support alone. The item statement and all three new statements are retained. A final dry run and push are required after this concrete repair.
