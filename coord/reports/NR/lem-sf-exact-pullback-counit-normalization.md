# Worker report: lem-sf-exact-pullback-counit-normalization

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-exact-pullback-counit-normalization.json: statement, split into seven proof steps; statement unchanged; full-item Mathlib verdict remains no match.
- citations.json: one verbatim statement excerpt for every node cited by every proof step (21 entries).
- report.md: this report.

No new nodes and no new Mathlib leaves. The sandbox initially contained only dispatcher metadata, so there was no earlier proof or report to replace. The item's existing Mathlib searches and all blueprint/source fields were retained; five actually executed NR searches were appended. searches.jsonl is the search command's original log. write_split.py is a sandbox-only JSON preparation script.

## Attachments

None. I searched the current read clone's lean/WeilConjectures for the exact blueprint id, derivedIso_exists, strictIso_exists, completedPullback, ordinaryToCompleted, and counit-normalization terminology. No declaration covers this item. The native SfImmersionCompletedPullbackComparison.lean locator in the imported source field does not name a file in this read clone, so it is not evidence of a finished proof. Other derived tensor/pullback counit-normalization declarations concern different functors and omit the strict augmented construction.

## WANTED

None. The proof uses the local Stacks sources and existing DAG statements, rather than an unavailable native Lean implementation.

## Corrections and source audit

The original node was a statement-only unsplit extraction, not a proof. Its statement is correct with the hypotheses as recorded: exactness of the transported functor and invertibility of the coefficient map are assumptions, not consequences claimed for an arbitrary scheme morphism. Its reference to an adic datum retains the finite/perfect-quotient requirements of def-weil-pbc-adic-coefficient-datum. No statement change or route departure is made.

The current main-20261015 blueprint prop-sf-localization-all-stages.md states the localization theorem but contains no proof. I read its full text, the unit and chapter records, and the existing parent immersion-comparison statement/proof dependencies. This split supplies the exact-pullback normalization subargument required by the returned localization Step 6; it does not attempt the localization triangle itself. The proof is marked agent-written. The supporting sources actually read are Stacks derived.tex Tag 015F (lemma-right-derived-exact-functor), Tag 06XN (lemma-find-existence-computes, explicitly its dual), Tags 0FND and 09T5 (pre-derived and derived adjunctions), sites-cohomology.tex Tag 0941 (lemma-derived-limit-is-ok), and proetale.tex Tag 099N (lemma-pushforward-Noetherian-case), especially clauses (2),(5). The last source supplies the completion context, not the counit equations proved here. No SGA source is used.

A potentially misleading shortcut has been avoided in the actual proof: equality of maps in a derived strict-tower category is not inferred from equality after all evaluations. The constant-tower equation is checked in that category using the counit normalization, and the augmented square follows from naturality there. Likewise no claim that arbitrary pullback preserves countable products or commutes with inverse limit is used. We apply derived limit to an already constructed isomorphism of towers.

## Not duplicates

No new nodes. The whole-DAG keyword searches, blueprint searches for exact pullback, exact functor and counit normalization, and the Lean searches led to reusing the existing exact-derived-functor, Kan-extension uniqueness, strict evaluation, constant-tower, quotient-augmentation, and derived-limit tools. The blueprint exact-derived-functor definitions are strictly less specific than this item; they do not assert the specified augmentation square and projection equations.

## Review by NR

I checked delivery-errors B through E against the final node, with the cited statements open. The split has seven arguments, all below 1100 characters, rather than new nodes restating the item's clauses. There are no new statement-only nodes to audit. Every uses entry is included in proof_deps, every cited node exists, and following their statement/proof dependencies does not return to this item. The statement dependency list was retained because each listed notion still occurs in the unchanged statement.

Step 1 uses lem-weil-pbc-exact-functor-derived-functor for its explicit assertion that the exact descent with its localization comparison is a LEFT derived pair on unbounded complexes; its right-derived clause alone would not suffice. It uses lem-sfb-right-kan-extension-unique-iso for the unique comparison with its counit equation. I read Mathlib CategoryTheory/Functor/KanExtension/Basic.lean lines 77–145 and Functor/Derived/PointwiseLeftDerived.lean lines 174–200: these substantiate the generic tools, but do not cover the full item. Composing the comparison into QG with Qm is an invertible change of the target of the universal property, as explained in the step. This verifies the orientation of xi e = Qm epsilon and the isomorphism assertion, without adding a hypothesis that the original counit is already invertible.

Step 2 uses the actual levelwise kernels/cokernels in lem-weil-tower-category-levelwise-abelian to verify the exactness of the tower functor, then the same two universal-property statements from Step 1. Naturality of m with each transition is written explicitly. This takes place in D(Tow(Mod(B))), not merely in Tow(D(Mod(B))).

Step 3 uses precisely the counit equation epsilon v_n = ev_n tau stated by lem-cbc-derived-tower-evaluation-normalization and its transition compatibility. I checked that the normalized equation is stated initially for objectwise K-flat flat-term representatives, so the step cites lem-weil-pbc-diagram-kflat-replacements to cover every unbounded tower and uses naturality along the replacement isomorphism. The indexing category is the small positive-integer opposite poset, meeting the diagram theorem's smallness hypothesis.

Step 4 uses the equation tau_(Delta P) b = Delta epsilon from lem-cbc-derived-constant-tower-normalization, the explicit exact-localization comparison of lem-weil-pbc-exact-functor-derived-factorization, levelwise exactness of towers, and the one-object case of diagram K-flat replacements. The displayed calculation compares the two entire maps after the same invertible Xi; no conservativity or faithfulness of derived evaluations is asserted. Since constant K-flat towers have K-flat flat-term evaluations, the cited b equation applies.

Step 5 uses def-weil-pbc-adic-coefficient-datum for the strict quotient tower computed on P and lem-cbc-strict-quotient-pullback-computation for the actual map w_P and its compatibility with changing representatives. It uses the b normalization again to identify beta with that actual map after epsilon_P. I checked the factors' domains: beta starts at Delta L K, a_K starts at Delta K, and E is evaluated at K_bullet. Naturality of E at a_K, followed by Step 4, gives the full written square. Quotient complexes need not be K-flat over B_X, and the cited quotient-computation statement specifically allows this.

Step 6 uses def-weil-pbc-completed-pullback for the strict augmented definition of alpha, prop-weil-pbc-rlim-functoriality for the functor applied to E, and lem-coef-derived-tower-counit-projections for the canonical derived adjunction Delta dashv Rlim. The ringed strict tower homotopy-limit theorem supplies its unbounded K-injective computation for the small ringed sites. I checked the latter node's statement supplies tower K-injective resolutions and computation by termwise limit, as required by the projection theorem. Under this normalized adjunction the unit is the compatible-resolution-map construction from the completed-pullback definition. Unit naturality gives the displayed equality after Step 5; no claim about a freely selected cone map is needed.

Step 7 uses the natural counit projections, explicitly asserted naturally in B in lem-coef-derived-tower-counit-projections, on the very morphism E_(K_bullet). This gives the written evaluation square for d, with Step 3 identifying its right side. The completed-pullback definition and the unbounded strict-tower theorem justify use of the same ambient formulas outside the complete subcategory. No claim that alpha is invertible is made. Thus an incomplete K does not invalidate the proof.

I checked the small cases g = identity, zero complexes/towers, a constant quotient tower (I = 0), and a general complex not assumed complete. For g = identity, the comparison is the one forced by the specified counits, so arbitrary choices of derived models cannot insert an unnormalized automorphism. Zero objects give the zero augmentation square. For I = 0 the same square is the constant-tower one. For an incomplete object the square and d still exist, while alpha can fail to be an isomorphism, consistent with the statement. There is no boundedness or product-preservation assumption to lose in any step.

The off-unit statements used as generic tools are declared in split_report.tool_uses with their exact roles. They supply formal derived-functor infrastructure without replacing the unit's localization route. Mathlib leaves are used directly as tools. The inherited search results and the new live search hits were read; totalLeftDerivedCounit, rightKanExtensionUnique and exact descent are ingredients rather than an attachment or a one-line Mathlib proof of the full item.

## Unfinished work

None in the stage-1 split. Delivery validation is recorded below after the required server dry run.

## Delivery validation

The required deliver.py --no-push completed successfully: OK (not pushed), preflight passed, initial dry-run commit 51fdd8740db. This includes the server check_dag and review_split checks. The finalized report is checked again before the direct delivery push. No Lean was written and no compiler, Lake or build command was run.
