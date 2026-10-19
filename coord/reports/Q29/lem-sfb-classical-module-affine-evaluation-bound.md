# Q29 stage-1 delivery: lem-sfb-classical-module-affine-evaluation-bound

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-classical-module-affine-evaluation-bound.json`: statement item, split into four steps; Mathlib verdict no match. Statement and statement dependencies unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement excerpt for each citation in each proof step.
- `report.md`: this report. `searches.jsonl` contains the five actual item searches run during this attempt; `write_split.py` is sandbox-only working material, not a project-file delivery.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree by the exact item id and by classical/evaluation/cohomology notions. The comparison file `SixFunctors/ProEtale/Comparison/LowerStarAcyclic.lean` has generic evaluation/localization and comparison results but no declaration asserting the item. Its injective-comparison-acyclicity theorem at lines 107–111 is itself sorry. No generic localization declaration alone supplies this item's field-dependent uniform bound. I did not treat the reference master source or any sorry declaration as a finished proof.

## WANTED

None. All sources needed for the split are present locally.

## Corrections and source audit

There was no existing sandbox item or report. I continued from the repository's unsplit Q88-created node and preserved its statement, dependencies, ancestry and historical searches. The blueprint's fixed-degree-truncation paragraph uses a classical sheaf bound on W; the imported item additionally specifies module-valued derived evaluation computed in the ambient X site. The proof now gives the missing bridge explicitly. In particular it does not assume that forgetting scalars sends injective module sheaves to injective abelian sheaves.

The unchanged statement is well-typed with its constant scalar map A to A_X(W), ordinary left modules, and common larger universe. The étale module bound has exactly the same field, prime, coefficient and dimension conventions. No statement dispute was needed. No chapter or unit record was changed, and the proof stays on the bounded-below-comparison/uniform-bound route which supports the unbounded comparison in the unit's first step.

## Not duplicates

No new nodes. Searched all blueprint nodes with `tools/blueprint_refs.py search classical` (60 matches) and `search evaluation bound` (zero), and read the related bound, comparison and localization statements across the DAG. `det-pe-unbounded-classical-bounds` concerns torsion abelian sheaves on the pro-étale site; it does not identify ambient module-derived evaluation. `lem-sfb-etale-module-affine-bound` concerns étale module cohomology; it is reused, not duplicated. The comparison formula is reused in the singleton-presentation special case, rather than made into a new lemma.

## Mathlib searches

The actual item queries, tools and results are appended to its `mathlib_searches` and are in `searches.jsonl`: LeanFinder in two phrasings, Loogle using the pro-étale topology and sheaf names, grep in AlgebraicGeometry/Sites, and LeanSearch. All five services/calls returned successfully. Read the returned signatures: general derived-category bounds, vanishing on an injective input, sheaf cohomology definitions, finite type/presentation predicates, and condensed-module constructors do not assert this geometric vanishing statement. Read Mathlib's SheafCohomology/Basic, RightDerived, DerivedCategory/TStructure, Sheaf/Generators and Sites/ElladicCohomology at the locations recorded in the item. In particular a conditional vanishing statement for an already bounded derived object does not establish the required bound. The inherited Q88 invalid Loogle pattern is preserved as historical data, with its original corrective search; I did not create or claim that old query as a new search.

## Review by Q29

I read the main-20261015 chapter record, the unit `sk-prop-ctf-finite-comparison`, the ancestor `det-ctf-finite-comparison-localizing` proof, and the source proof of `det-pe-unbounded-classical-unit`. The latter's Fixed-degree truncation paragraph is the exact place where the bound is needed. I also read the current module classical-equivalence proof and the bounded-below comparison proof. For the localization argument I read Stacks `sites-cohomology.tex`, Tag 03F3 (`lemma-cohomology-of-open`), including its proof by restriction of injectives. For coefficient safety I read Tag 03FD (`lemma-cohomology-modules-abelian-agree`); it explains why an unqualified claim about underlying injectivity would be inappropriate. Stacks `proetale.tex`, Tag 099W (`lemma-compare-cohomology`), explicitly supplies the abelian comparison underlying the already-existing module comparison node. There are no new-node sources to check.

Step 1 uses the statement of `lem-weil-pbc-ring-sheaves-grothendieck` for small-site categories of modules over ring sheaves and the statement of `lem-sp-grothendieck-enough-injectives` to obtain resolutions. Smallness and coefficient universes were fixed in the item, not imposed as new mathematical hypotheses. The statement of `det-pe-classical-sheaves-modules` explicitly says its essential image is the full category of classical modules for every discrete commutative ring. A is precisely such a ring. Thus it really gives H isomorphic to nu_X^*G, without assuming constructibility or finiteness of G.

Step 2 uses `lem-weil-pbc-etale-inverse-image-restriction`, whose statement gives a natural abelian restriction isomorphism for every étale w, and `lem-pe-constant-left-module-inverse-image`, whose statement identifies the underlying abelian inverse image, the same constant scalars, and compatibility with localization. Naturality with each scalar endomorphism is written out to check linearity; no extra lemma is hidden in the coefficient change. The statement of `lem-sfb-etale-module-affine-bound` supplies exactly the displayed vanishing for w^{-1}G, with the same e_X and all the same hypotheses. It applies to every G, so no flatness or finite-generation condition is smuggled in.

Step 3 uses the affine formula from the statement of `sk-prop-sf-comparison`, not its proof. Its index category is explicitly chosen as the one-object identity category; this is nonempty, small and cofiltered and its filtered derived colimit is its sole value. Thus no continuity theorem or arbitrary-colimit interchange is being silently invoked. G[0] meets the bounded-below input requirement. `lem-weil-pbc-right-derived-plus-injective` clause (2) states that a bounded-below injective complex computes the right-derived functor, so taking degree-q cohomology of the comparison is exactly the module cohomology in step 2. This is a bounded-below comparison only; the unbounded comparison that this item supports is never used.

Step 4 uses the actual statement of `lem-weil-pbc-proetale-restriction-injectives`: the pro-étale site of W is the slice, and restriction is exact and preserves injective constant-coefficient module sheaves. Since the item already regards w as a pro-étale object and A is finite discrete, its hypotheses hold. The resolution notion is `def-sp-injective-resolutions`. The proof displays the identical complexes and constant scalar actions at W, giving the ambient E_W computation in the item, not merely a vanishing statement in some unspecified smaller category. The degree inequality q>e_X and the constant bound are preserved.

I checked delivery-errors B–E against the node and these source statements. B: self-contained original statement, definition dependencies retained, ordinary TeX written once, no new unsplit nodes with hidden proofs, exact ancestry preserved, no false Mathlib leaf or invented query. C: every non-elementary input is a cited statement; each cited file was opened, every used conclusion is present in its statement, and `citations.json` was checked by literal substring against those statements. Generic off-unit tools are declared with their precise purpose in `split_report.tool_uses`; no maintainer-owned `tool_uses` field was added. D: the four steps carry the descent, singleton comparison and explicit resolution computation, rather than moving the conclusion to a new node. E: verified the same coefficient category at every arrow, the given affine étale presentation, the bounded-below hypothesis and the unchanged degree bound. There are no non-elementary steps longer than 2000 characters (lengths 642, 924, 1111, 985).

Edge cases checked: X empty with d_X=0 and e_X=1 (then any W is empty); W empty for nonempty X; H zero; the zero coefficient ring; X the spectrum of a finite or algebraically closed field; w identity when X is affine; and arbitrary non-finitely-generated G. The proof works through the same cited comparisons in all these cases. It claims nothing at q=e_X. The singleton presentation has identity transition maps, so it needs no additional finiteness or cofinality argument.

## Unfinished work

None in the one-level split. The existing étale-bound item remains an existing DAG dependency for its own worker, not a new hidden obligation or a duplicated clause. Server validation and direct delivery are performed after this review.
