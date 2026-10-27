## Worker report

Files written:
- `dag/nodes/sec-purity-real-sheaves/lem-a1-representable-etale-kernel-relation.json`: statement item, split into five steps; no exact Mathlib match for the whole statement.
- `citations.json`: all four step/node citations with verbatim statement excerpts.
- `searches.jsonl`: five actual searches through the required msearch command, including two distinct LeanFinder phrasings; all services answered.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. The argument reuses `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`, an existing Mathlib leaf, and the existing definitions of the fppf site, scheme fibre product and scheme-test representable morphism properties.

## Attachments

None for this item. Searches under `lean/WeilConjectures/` by the exact blueprint id and by representable/etale/kernel-pair terminology found no declaration stating all clauses. The generic `CategoryTheory.bijective_yoneda_app_id` in `WeilConjectures/Mathlib/CategoryTheory/Yoneda.lean:90` belongs to the existing `lem-pc-yoneda`, not to this item. Its statement and proof were read; it is not needed by the final split.

## Literature and route

Read Stacks `spaces.tex`, Tag 0262, `lemma-space-presentation`, statement and proof at lines 1171–1211. Its first paragraph identifies the sections of R and gives the etale projections. Read `sites.tex`, Tag 00W2, `lemma-limit-sheaf`, statement and gluing proof at lines 1680–1712, for the sectionwise limit identification. Also read `spaces.tex`, `definition-relative-representable-property` at line 497 and its following warning distinguishing the three meanings of surjectivity. The item's existing `def-trf-algebraic-space` explicitly spells out the required scheme-test meaning, including surjectivity. The additional diagonal and interchange formulas are written out rather than hidden behind the expression “equivalence relation”. No coequalizer assertion is needed or used.

Read the chapter record `sec-purity-real-sheaves` and unit `sk-p-real-rankin`; this is an auxiliary U/R presentation in the existing 03BZ/03XW branch below `lem-a1-affine-hc0`, as recorded by the ancestor and the item's existing `blueprint.from.place`. Read the current main-20261015 ancestor text, which states the compact-support vanishing assertion. The delivery changes neither the unit nor the ancestor. `blueprint_refs.py ancestor` returns `lem-a1-affine-hc0`; whole-blueprint searches for `kernel relation`, `limit sheaf`, and `representable etale kernel` found no duplicate of this item. The two results for `limit sheaf` concern adic coefficients and Tate twists, not the kernel relation. Whole-DAG source/keyword searches located the existing sectionwise limit theorem and Yoneda facts; no replacement node was introduced.

WANTED: none.

## Corrections and unfinished work

The imported item had no proof. Its statement, statement dependencies, citation records and provenance were retained. The split adds the full assembly argument and fresh logged Mathlib searches; no STATEMENT-DISPUTED correction is necessary. The statement correctly assumes a represented kernel pair and does not assert the diagonal of an arbitrary sheaf is representable. There is no unfinished mathematical part of this split.

## Mathlib audit

The five newly logged searches are copied verbatim to `mathlib_searches` with their actual output digests and verdicts. LeanSearch and Loogle find `CategoryTheory.IsKernelPair` and its generic universal-property API. The grep locates `IsKernelPair.equivalenceRelation` in `Mathlib/CategoryTheory/EquivalenceRelation.lean:106`, whose body at lines 106–115 was read, and `IsKernelPair`/`lift` in `Mathlib/CategoryTheory/Limits/Shapes/KernelPair.lean:55,79`, whose source was also read. These give categorical relation constructions, with no scheme-test etale/surjective conclusion. LeanFinder's first query gives Zariski `Scheme.LocalRepresentability.representableBy` and the scheme-only `Scheme.instHasPullbacksEtale`; the second gives scheme gluing relations, the etale category and separated morphisms. Their displayed signatures concern a different base category or only part of the conclusion. Thus none is an exact match or a one-line specialization for the entire item. The already existing sectionwise sheaf-limits Mathlib leaf is cited rather than recreated.

## Not duplicates

No new nodes were created. The existing sheaf-limit theorem is strictly more general than the limit fact used in step 1 and is reused. The Yoneda nodes are also reused as search evidence only; no duplicate or new clause-node was added.

## Review by Q05

I checked the source and every cited statement with the files open. The item generalizes only the first paragraph of Tag 0262: the algebraic-space hypothesis there supplies representation of R, whereas this item already assumes that representation and that p is representable surjective etale. Inspection of the paragraph shows that the diagonal of F is not otherwise used. The theorem's extra surjectivity conclusion for s and t follows directly from the scheme-test hypothesis, not from a claim that sections lift globally. There are no new statements requiring a separate source audit.

Step 1 cites `def-pc-fppf-site` for the actual site and `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`, clause (2), for evaluation of its sheaf pullback cone. I checked that the latter applies to sheaves of sets on any site and a small indexing category: the cospan is finite, and the site uses the existing size convention. The morphism p is a morphism of sheaves in the stipulated scheme-test sense, so the cone is in that category. The quoted theorem actually gives the bijection for any limit cone, not just existence of a preferred limit. The displayed restriction formula uses ordinary associativity and naturality of p, and explicitly checks that restricted pairs remain compatible. This is the only non-elementary step, and its lemma is cited.

Step 2 cites `def-pc-fibre-product`, whose statement gives the scheme product with projections and its universal property. It supplies j=(s,t). Cancellation follows by taking the two projections and using the already proved injectivity of beta_T. Reflexivity, symmetry and transitivity are the three written equality arguments; no external equivalence-relation theorem is being assumed. Testing all S-schemes is sufficient for scheme monicity here: any pair of scheme maps to R equal after j automatically has the same composite to S and is therefore a pair of S-morphisms for that induced structure.

Step 3 cites `def-trf-algebraic-space` only for its explicit definition of representable morphisms and their etale/surjective scheme-test properties. I checked the exact sentence, which applies to maps of sheaves, without requiring that either sheaf be an algebraic space. The test scheme is U and the test morphism is p. Both orientations of the cone are pullbacks because the two bottom maps are the same p; swapping the components of every compatible pair gives the reversed universal property. Thus s and t are themselves test projections. This is an application of the definition and the stated universal property, not an uncited stability theorem or a statement about surjectivity of U(T) to F(T).

Step 4 uses no external node: beta_U is a bijection already proved, and its inverse at (id_U,id_U) is literally an element of R(U), hence the required S-morphism U to R. Its projection identities follow immediately from beta_U, and step 1 checks its diagonal effect on every T. Step 5 likewise takes the inverse at (t,s) in R(R); this pair is compatible by the cone equation. The two projection equations imply beta_R(i squared)=beta_R(id_R), which proves the involution by injectivity. The final composition formula proves the actual factor interchange on all sections. Neither step hides an invocation of full faithfulness or of a groupoid theorem.

I tested the empty-scheme case: U empty forces R empty by its maps to U, and the diagonal, interchange, empty-test singleton sections and other empty sets obey the formulas. For p an isomorphism, R is the diagonal relation. For p from a nontrivial etale covering scheme to a represented sheaf, R(T) can be empty above particular pairs unless their images agree, precisely as stated. A surjective etale scheme need not have a section over an arbitrary test scheme, so no pointwise surjectivity claim is made. The argument works with nonseparated schemes and no properness, finiteness or connectedness assumptions. No extra hypotheses were added.

Against delivery-errors B–E: all statements remain self-contained, existing definitions are cited for the notions they actually define, all four node citations have verbatim excerpts in citations.json, there are no new leaf claims or nodes to split, no clause was relabelled as a child, and the explicit formulas account for every naturality/identification assertion. The entire five-step proof is 2352 characters, and no individual step exceeds 2000 characters or hides a separate non-elementary lemma. No mathematical correction was needed after these checks.
