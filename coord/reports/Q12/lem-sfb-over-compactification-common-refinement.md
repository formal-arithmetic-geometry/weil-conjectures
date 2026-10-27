# Q12: lem-sfb-over-compactification-common-refinement

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-over-compactification-common-refinement.json`: split statement; unchanged mathematical statement; no Mathlib match.
- `citations.json`: 14 checked verbatim quotations, one for each cited node in each proof step.
- `report.md`: this report. `searches.jsonl` is the search command's actual log; the sandbox also contains the script used to prepare these files.

New nodes: 0. New Mathlib leaves: 0. No Lean files written or compilation tools run. No repository or launcher files changed.

## Attachments

None. `lean/WeilConjectures/Compactification/Refinement.lean:124`, `AlgebraicGeometry.Compactification.exists_overRefinement`, still has `sorry`. The project search for the item id returned no declaration. The source's completed `Compactification.exists_common_refinement` and `isPullback_infFst`/`isPullback_infSnd` concern underlying schemes, not the `OverRefinement` structure and its pullback in `Over S`, so they are not claimed as an exact attachment. Their geometric content is already represented by existing nodes, which this split reuses.

## WANTED

None. All sources used are available locally.

## Corrections and scope

The statement agrees with the actual signature and docstring of the upstream sorried declaration, including its qcqs base and both finite-type separated structure morphisms. No statement dispute or change was needed. The initial `stmt_deps` cited `sk-def-sfb-dc-setting`, which is a positive-characteristic field and coefficient setting absent from this arbitrary-qcqs-base statement. I removed that dependency and listed the actual definitions used by the statement instead. This adds no hypotheses. Historical source, blueprint and Lean records are preserved.

The item is a supporting geometric lemma, not the key definition of its lower-shriek unit. No unit binding is changed. I read the six-functors chapter, lower-shriek unit and current blueprint text. The chosen-compactification clause is the ancestor place served by this lemma; its only displayed unit step concerns inclusions of constructible categories, which this delivery does not replace. The geometric tool is the same closure-of-graph construction as the imported item's parenthetical prescription. Both generic non-definition tools from the Nagata chapter are declared in `split_report.tool_uses`.

## Not duplicates

No new nodes were created. Whole-DAG and blueprint searches for common refinement, closure of the diagonal, and OverRefinement found the existing `det-nagata-refinement-common-dense`; the imported item's `same_as` already names it and is retained. The cartesian theorem is already `lem-nagata-dense-refinement-cartesian`. I reused both, rather than restating either as a new child. The only additional argument is the explicit transfer of their data to schemes over the original base.

## Review by Q12

I read the item against the actual `OverRefinement` fields and the `exists_overRefinement` docstring and signature in `lean/WeilConjectures/Compactification/Refinement.lean`, and the definitions `overObj`, `overI`, `overG` in `Over.lean`. I read the common dense refinement's current DAG statement and its current blueprint statement and proof, in `main-20261015/.../det-nagata-refinement-common-dense.md` and `.proof.md`. I also read the source implementation in `CommonRefinement.lean` and the existing cartesian theorem in `RefinementPullback.lean`. The source implementation uses the same graph-image object; no proof fact is taken only from the internals of a cited node. The input compactifications need not be dense. There are no new-node sources to review.

Step 1 verifies the hypotheses needed before the geometric theorem is applied. `def-weil-finite-type-morphism` explicitly equates finite type with local finite type plus quasi-compactness. Clause (b) of `lemma-nagata-finite-type-to-separated-target` really gives finite type, not just local finite type, because the second arrow here is the separated structure map of Y. `lem-weil-pbc-separated-cancellation` clause (b) applies to the separated composite X to S. `lem-pc-separated-quasi-separated` applies to Y to S, and clause (2) of `lem-weil-pbc-qcqs-morphism-permanence` gives each absolute qcqs property of Y from S. I opened and read all five statements. The source checks were Stacks schemes.tex Tags 01KV, 01KU and 03GI and morphisms.tex Tag 01T8. This step specifically prevents the mistake of applying the common dense theorem over a base not yet known qcqs.

Step 2 uses exactly the pairwise part of `det-nagata-refinement-common-dense`, with its letter S instantiated by our Y. Its statement supplies the graph-image object, the quasi-compact dense open immersion, the proper structure map and both refinement triangles. The scheme-theoretic-image definition explicitly identifies the closure of a locally closed subscheme with that image, so it justifies the item's parenthesis. No finite-family induction is used. This is a citation of a pre-existing geometric tool, not a new node relabelling the requested theorem.

Step 3 checks properness separately because the common dense node's explicitly enumerated refinement conditions are triangles and the boundary condition. `lem-weil-pbc-proper-over-separated` says precisely that a Y-map from a proper Y-scheme to a separated Y-scheme is proper. Its base here is Y, not S: the available proper maps are p and p_k. Properness implies separatedness by the proper-morphism definition. I read Stacks morphisms.tex Tag 01W6, label lemma-image-proper-scheme-closed, including part (2). The two definition statements for compactifications and schemes over a base give exactly the structure-map conventions used. The two displayed composition equations establish that i and each q_k are S-morphisms; the equality over Y is already supplied in Step 2. Nothing about coefficient categories is invoked.

Step 4 uses `lem-nagata-dense-refinement-cartesian` under precisely its stated hypotheses: the two triangles, quasi-compactness of i, and schematic density of i. Its statement explicitly says no density or quasi-compactness assumption on the target open is needed. I checked its source declaration and the project's standard-axiom guard by reading; I ran no compiler. The remaining passage to the slice category is written out using only the universal property in `def-pc-fibre-product` and the definition in `def-weil-scheme-over-base`. The unique underlying lift t is the already given S-map u because its composite with the identity of X is u. Thus it is a morphism over S, and uniqueness holds there as well. This avoids citing a pullback-preservation theorem in the wrong direction or merely asserting a transport. The square has the required orientation with the identity of X and the two open immersions.

Step 5 just assembles the very data established in Steps 2–4 into the fields of OverRefinement, twice. It is elementary and creates no new claim. Every step is below 2000 characters; none hides a long comparison argument. The 14 citations were produced from the current node statements with a literal substring assertion for every quote, so each quote is verbatim. I also checked that neither geometric tool depends on this item, and that all cited nodes are unmerged.

For small cases I checked X empty (the graph image and the resulting common compactification are empty), S or Y empty (the existing maps force the relevant sources to be empty), identity compactifications, and compactifications with extra proper components disjoint from X. No input density is used, and the closure construction discards those extra components as needed. Nonreduced schemes remain allowed: scheme-theoretic density and scheme pullbacks are used, not reduced topological closures. The slice-category universal-property check is valid for every test S-scheme without a finiteness assumption. I checked B–E against these concrete objects: all non-elementary inputs are existing cited statements, no new statement is only a clause of the item, no hypothesis is supplied by a definition-only citation, and no forbidden SGA route is used.

I read the actual outputs of five new recorded Mathlib searches: LeanFinder twice with different phrasings, Loogle, grep in AlgebraicGeometry, and LeanSearch. Loogle reported an unknown scheme Compactification identifier; grep had zero hits; the semantic results cover affine-transition limits, proper projections, diagonals and general immersion pullbacks, but not this common compactification over a base. I did not record these as unavailable: the services answered. The existing historical searches are retained, and only queries actually present in this item's search log are appended.

## Dry-run repairs

The first dry run requested a longer quotation for `lem-pc-separated-quasi-separated`; I replaced its short conclusion fragment with the whole literal statement, including the separatedness hypothesis. The mathematical step is unchanged. The server then rejected the phrase “the item's parenthesis” as non-self-contained; I replaced it with the explicit closure of the image of X in the product of Z_1 and Z_2 over Y.

## Unfinished work

None within this stage-1 split. The existing upstream Lean theorem remains sorried; writing its Lean proof is outside this authorized stage.
