# Stage-1 report: lem-weil-pbc-distinguished-diagram-lifting

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-distinguished-diagram-lifting.json`: statement, split in six steps; no Mathlib match.
- `citations.json`: one entry for every node cited in every proof step, with the verbatim statement containing the facts used.
- `report.md`: this report.

No new nodes and no Mathlib leaves. All statement dependencies, blueprint ancestry, original statement, original source and inherited search records are retained. The original sandbox node equaled the current shared node before editing; the interrupted attempt had no completed split or report. The existing searches.jsonl was read and reused, including both LeanFinder phrasings and the successful corrected Loogle query. The supplementary grep search is logged there too. No compiler, Lake, project git command, live write, or agent delegation was used.

## Attachments

None. Searched WeilConjectures and Comparator in the read-only slopmaster2 tree for the item tag/name and for common-stage, finiteStage, PairCategory and the relevant finite-diagram notions. No declaration states this simultaneous lifting theorem. PoincareDuality/Transport.lean explicitly says its source lacks the finite-E colimit category; its finite-reduction result does not supply an attachment. The item has no Lean declaration in its audit or upstream name table.

## WANTED

None. The proof expands the current blueprint's implicit argument, and is correctly marked agent-written. No SGA source is used.

## Problems and corrections

The imported proof was empty. The ancestor's TR2--TR4 proof silently assumed simultaneous distinguished-row lifting. The split supplies that argument without assuming the pair category already triangulated and without invoking its ancestor (which depends on this item). In particular, it does not infer distinguishedness by reflection through an inclusion. It extends native cone triangles by exact transitions, then realizes their witness isomorphisms at the common stage.

The statement is unchanged; no statement dispute was found. The finite-stage triangulation and exact structures are hypotheses already present, so no reconstruction of the integral or rational categories is needed here. The first draft was replaced to expose the last-arrow coherence formula and the triangle witness equation explicitly. Cone independence is not needed as an extra black box: its relevant transport clause is proved directly using exactness, the prescribed comparisons and finite-stage TR1.

## Unfinished work

None in this one-level split. Existing dependencies retain their own queue states.

## Not duplicates

No new-node pairs exist. Searches of the whole DAG and blueprint for distinguished, common-stage, simultaneous and finite diagram found the existing calculus, common-stage cones, cone independence, det-sp-qbar-finite-descent, and lem-weil-pbc-filtered-colimit-category-finite-lift. The latter two give finite-diagram descent but do not assert simultaneous distinguished-row witnesses in this particular pair category. They are not substituted for the actual pair-category calculus. The ancestor Verdier-axioms node uses this item and cannot be cited as a proof dependency.

## Review by Q32

I read coord/brief-stage1.md, stages/1-dag.md, the three levels in SETUP.md, GOAL.md, coord/dag-sync.md, the worker role, tools/README.md, and all of delivery-errors B--E. I read the smooth-purity chapter record, sk-prop-sf-cbc unit record, its current main-20261015 section text, and the full ancestor thm-weil-pbc-verdier-axioms.proof.md, especially TR2, TR3 and TR4. This auxiliary is not the unit key statement; I changed no chapter or unit record. Its inherited chapter/unit binding is retained. The proof implements the ancestor's common-stage route, rather than replacing any unit-level step. The off-unit calculus and scalar-extension statements are declared as generic tool uses in split_report.

For Step 1 I opened def-weil-pbc-common-stage-cones and def-weil-pbc-triangles-with-shift. The former defines distinguishedness by an actual triangle isomorphism to a native common-stage cone triangle, including its inverse-sigma third arrow; the latter gives exactly three components, the third commutation relation with a[1], componentwise composition and the characterization by component isomorphisms. This justifies selecting the witnesses and listing all their equations. It is elementary unpacking of those definitions, not a new existence theorem. Each row contributes finitely many objects and arrows, so the enlargement stays finite.

For Step 2 I read the full def-weil-pbc-finite-stage-pair-category statement: representatives exist at finite overfields, composita give upper bounds, the transition formula is conjugation by the associators, T_{E/E} is literally the identity, and the operations are common-stage operations. This supplies the precise representatives and object lifts, with the requested M0 included. A finite extension is finite-dimensional over Q_l, never a finite field in the cardinality sense. Repeated vertices have exactly one fixed pair, hence the same chosen lift.

For Step 3 I checked the full prop-weil-pbc-common-stage-calculus statement, not its proof: it asserts additive transport, transitivity, representative-independent operations, eventual equality for finite diagrams, and the displayed formula for a shifted arrow. I also read prop-weil-pbc-scalar-extension, whose statement supplies compatibility of sigma with the associators. The step expands finite expression trees, uses the displayed cancellation for one shift, and iterates it; zero, addition and negatives use the additive operations already asserted. Equality of classes does not imply equality at the initially chosen field: the proof explicitly takes the further equality witnesses, then their common overfield. All witness inverse equations are among these equations.

For Step 4 I read the exact-functor clause of def-weil-triangulated-category and the exact scalar-extension and coherent sigma clauses of prop-weil-pbc-scalar-extension. Both apply for the same noetherian finite-dimensional T with ell invertible as assumed in the item. I checked the native cone formula in def-weil-pbc-common-stage-cones, then wrote the precise identity obtained by transporting its inverse-sigma arrow and multiplying by sigma at M. Its two sides land in X_M[1]; the third-object source is T_{M/N}C. Associators identify the first two objects, and finite-stage TR1 transfers distinguishedness. The finite-stage structure is the one explicitly assumed by the item, not an arbitrary extra one.

For Step 5 the calculus gives the shifted representative of a. The inverse identities make the three lifted components isomorphisms, and the displayed multiplication by sigma converts exactly the raw third triangle equation to the required stage equation. The first two equations require no correction. The triangle-isomorphism characterization is stated by def-weil-pbc-triangles-with-shift, and finite-stage closure under such isomorphisms is explicitly TR1 in def-weil-triangulated-category. This proves each selected row distinguished without a circular appeal to the ancestor theorem.

For Step 6 I checked the identity-representative comparisons against the pair-category definition. Both composites are identities, naturality is the common-stage formula, and the shifted rho equation follows from the calculus plus the normalized transition of scalar extension. The row's last arrow then recovers the raw p_M because sigma^{-1} cancels sigma. These equations also establish recovery for all composite expressions and repeated shifts. I did not take this naturality from a definition node that only names a construction: its elementary representative computation is written out here.

I tested the assertion with empty data (M=M0 is allowed), no marked rows, a single native cone row, overlapping rows sharing vertices, an identity or zero arrow, inverse witness arrows, and a shifted object appearing also as an original specified object. In the last case its raw lift and the shift of the unshifted lift are compared by sigma, not asserted literally equal. No unwanted faithful/fullness hypothesis or countable/infinite diagram is used. All steps are below 2000 characters; the two possible hidden comparisons (native cone transport and the shifted third witness equation) have explicit formulas in Steps 4 and 5 and use precisely the cited coherence clauses.

I read Mathlib CategoryTheory/Triangulated/Functor.lean (the mapTriangle definition and lines 252--299), Localization/Triangulated.lean (lines 88--102 and 135--150), TStructure/TruncLTGE.lean (lines 71--96), and Limits/Types/Filtered.lean (lines 35--100) to assess the recorded search hits. The localization lemmas concern individual triangles; map_distinguished_iff requires full faithfulness, not assumed here; the t-structure lemmas require truncation bounds and do not describe finite-stage lifting. Filtered-colimit equality lemmas alone do not assert distinguished-row witnesses. I also read Stacks derived.tex definition-triangulated-category, Tag 0145, for TR1 and the exact third-arrow convention; its result is already represented by the cited definition node, so no new Stacks node is appropriate.

The B--E audit found no new self-contained statement to check, no duplicate to introduce, no unsupported tagged result, no relabelled conclusion node, no dependent ancestor citation and no changed coefficient category. Every node cited by a step has been opened and its statement copied verbatim into citations.json; the mathematical facts taken from it are explained above. Non-elementary Steps 3 and 4 cite the existing calculus and exactness results. The other steps are explicit few-line definition and identity manipulations.
