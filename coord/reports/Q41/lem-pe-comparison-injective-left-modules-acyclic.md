# Stage-1 report: lem-pe-comparison-injective-left-modules-acyclic

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-comparison-injective-left-modules-acyclic.json`: statement, split; no matching Mathlib theorem. Five proof steps, unchanged statement, no new nodes.
- `citations.json`: all 19 step/node pairs, with verbatim statement excerpts.
- `searches.jsonl`: six searches actually run through msearch.py; their outputs were read and independently recorded in the item.
- `prepare.py`: sandbox-only preparation script.

## Attachments

None. The project's generic theorem `AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`, `WeilConjectures/SixFunctors/ProEtale/Comparison/LowerStarAcyclic.lean:107-111`, ends in `sorry`. It is not an attachment. Searches of the project by the item id, comparison acyclicity, and injectives found no completed declaration proving the item.

## WANTED

None. All mathematical sources used are present locally.

## Findings and corrections

The dispatched item is absent from `/home/ubuntu/weil-newtargets-shared/dag/nodes`, including a search without ignore filters. The exact existing node is present in the authoritative read-only mirror `/home/ubuntu/weil-nt-live-dag/nodes/sec-proetale-coefficients/lem-pe-comparison-injective-left-modules-acyclic.json`; that is the copy used. No shared or live file was edited and no git command was run in the shared checkout. Delivery preflight must determine whether the current server base contains this existing node.

The statement is correct and unchanged. In particular, it allows an arbitrary associative ring, not merely a finite ring or a commutative ring. Existing `sk-lem-pe-injective-acyclicity` and `det-pe-injective-acyclicity-reduction` explicitly require a commutative ring; `lem-weil-pbc-comparison-grothendieck-injective-acyclicity` requires a finite ring; and the affine module comparison node depends on a finite-ring coefficient definition. None was used as if it supplied arbitrary coefficients.

The tempting shortcut that the underlying abelian sheaf of an injective module sheaf is injective is invalid in general: even over a point, an injective F_p-module need not be injective as an abelian group. Instead Tag 03FD, already stated by the existing module/abelian evaluation comparison node for a sheaf of rings without any commutativity hypothesis, identifies cohomology. This permits use of the independently split abelian comparison Tag 099W.

The item's source field now identifies the actual extension argument: Tags 099V and 099W, with 03FD and 03F3. The proof is marked agent-written because this combination extends the abelian comparison to arbitrary left-module coefficients. No new assertion is attributed verbatim to Stacks. Historical searches in the copied item were replaced by this worker's six actual, logged searches. The exact statement, blueprint ancestry, creation metadata and Lean audit are retained.

## Blueprint and duplicate searches

Read the current `sk-prop-sf-comparison/_section.md` and its `sk-prop-sf-comparison.proof.md`, the chapter record, the unit record, and the separate injective-acyclicity unit. The current comparison proof's first paragraph needs precisely comparison acyclicity of pulled-back injective module terms. The five steps supply that input and do not assume the parent comparison theorem.

Searched the whole DAG and blueprint for comparison injectivity, cohomology comparison, and the tags 03FD, 099V and 099W, including `tools/blueprint_refs.py search 'injective acyclic'`, `search 'cohomology comparison'` and `search '099V'`. Existing nodes were reused. No blueprint node found states this exact arbitrary-left-module result in another form, so `same_as` remains empty. The shared ancestor command cannot find the item because of the stale checkout; its copied ancestry correctly points to `sk-prop-sf-comparison` directly. The proof location is now explicit. No unit realization fields are appropriate: this item is an auxiliary input, not the unit's key statement.

## Mathlib searches

Ran leanfinder twice with different phrasings, loogle, leansearch, a whole-Mathlib comparison/acyclicity grep, and a second focused grep in CategoryTheory, all through msearch.py. All services responded successfully. Read the hits and the promising generic declaration `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ`, `Mathlib/CategoryTheory/Abelian/RightDerived.lean:153-159`. Its input must itself be injective, which is not asserted for the comparison pullback; it is the generic injective-vanishing tool already present in the DAG, not a proof of this item. The other hits concern underived pushforward, sheafification, locally injective morphisms, étale morphisms and category structure. No matching leaf was found.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. In particular no new node restates the item, its affine case, or its positive-cohomology vanishing clause.

## Tool uses

The item's `split_report.tool_uses` explains every statement used from outside the unit. These are the arbitrary-ring category and cohomology tools, the two localized-site identifications, the commuting inverse-image square on abelian sheaves, and the independently established abelian comparison. They prove the coefficient-extension input inside this unit, rather than replacing its derived-unit or affine-continuity route. Only the first sentence of the pro-étale restriction node is used, identifying the localized site; its finite-coefficient module infrastructure is not applied to arbitrary rings.

## Review by Q41

I read Stacks `proetale.tex` at labels `lemma-affine-vanishing` (099U), `lemma-relative-comparison` (099V), and `lemma-compare-cohomology` (099W). In particular 099U and 099V are stated for abelian sheaves, and 099W compares cohomology for every abelian sheaf, not just injectives. I also read `sites-cohomology.tex` at `lemma-cohomology-modules-abelian-agree` (03FD) and its proof, and at `lemma-cohomology-of-open` (03F3). Both work over any sheaf of rings; neither requires commutativity, flatness over Z, or injectivity after forgetting scalars. There are no new nodes with sources to review.

For step 1 I opened `lem-weil-pbc-ring-sheaves-grothendieck` and checked that it explicitly allows noncommutative ring sheaves and left modules, and `lem-sp-grothendieck-enough-injectives` supplies exactly the promised resolutions. The common enlarged universe in the item contains both small sites and the coefficient values, as required. The identification of the underlying abelian inverse image follows directly from the scalar-action construction specified in the unchanged statement.

For step 2 I opened all six cited statements. The comparison definition includes the étale objects in the pro-étale site. The étale restriction statement applies to abelian sheaves and every étale map; the pro-étale restriction statement's first sentence identifies the site with the slice. The comparison-pullback node gives exactly the inverse-image square being used, applied here to abelian sheaves. I also checked the localized-ringed-site and pro-étale inverse-image definitions. The step writes the forward and inverse maps of the restriction/base-change adjunction using a projection and a graph; this proves, rather than assumes, that the pro-étale inverse image is slice restriction. Thus the formula on W involves only abelian inverse images, and no finite-ring or commutative-ring module clause is smuggled into this step.

For step 3 I checked that the 03FD node is objectwise on an arbitrary small ringed site, with enough injectives provided by step 1; the injective-vanishing Mathlib leaf applies to module evaluation into Ab with the injective input I. The localization node is explicitly for abelian sheaves and identifies evaluation with global sections on the slice. The étale-site localization node, despite its name ending in `open`, explicitly allows every étale object. Consequently the conclusion is vanishing of cohomology of F restricted to W, without asserting injectivity of F.

For step 4 I checked the entire statement of the abelian comparison node: it applies to every scheme W and every abelian sheaf F restricted to W. Localization and 03FD then identify the resulting pro-étale cohomology with derived module evaluation on X. This is the essential coefficient change, and every non-elementary input is a cited node. I traversed the existing dependency closures of the abelian comparison (532 nodes) and of 03FD (135 nodes); neither reaches this item, `sk-prop-sf-comparison`, or `sk-lem-pe-injective-acyclicity`, so this coefficient route is independent of the module theorem being proved.

For step 5 the named definition of injective resolutions supplies J, while the separate definition of a left exact additive functor and its right derived functors gives exactly the resolution formula for derived evaluation and direct image. I corrected this citation during self-review: the resolution definition alone does not state the derived-functor formula. The comparison direct image is restriction on precisely these objects. The category-of-modules statement supplies sectionwise kernels and sheafified cokernels. Since image equals kernel on every étale object, the presheaf quotient is already zero; its sheafification is zero. This is the complete elementary passage from exact section complexes to exact module-sheaf complexes, not an unsupported invocation of a general higher-direct-image comparison theorem.

I checked B–E against the finished node and citation file. Every citation uses its statement, not its proof. The arbitrary ring, small-site universe, left-module direction, positive degree, and choice of injective category agree at every application. No additional coefficient or geometric hypothesis is introduced. Small cases include the empty scheme (all relevant section/cohomology groups vanish), the zero ring (only the zero module sheaf), a point, arbitrary noncommutative matrix rings, and rings with torsion additive groups such as F_p (the latter rules out the erroneous underlying-injectivity shortcut). The proof needs no geometric stalk conservativity, SGA, finite presentation, or affine basis argument.

## Unfinished work

No mathematical substep remains. Delivery and independent second reading are left to the prescribed tools and next worker; this worker runs only the required no-push dry run.


## Second reading by Q41

I independently opened the item, every cited node statement, the current main-20261015 comparison unit statement/proof and chapter record, Stacks proetale.tex at 099U (lemma-affine-vanishing), 099V (lemma-relative-comparison), 099W (lemma-compare-cohomology), and sites-cohomology.tex at 03F3 (lemma-cohomology-of-open) and 03FD (lemma-cohomology-modules-abelian-agree), including their proofs. The item's arbitrary associative unital coefficient ring, left-module convention, arbitrary scheme, common small-site universe, and all positive degrees agree with the claimed coefficient extension of these sources. The statement remains unchanged. The finite-ring clauses of the comparison definition and the commutative-ring acyclicity nodes are not used as arbitrary-ring theorems.

- Step 1: checked against lem-weil-pbc-ring-sheaves-grothendieck and lem-sp-grothendieck-enough-injectives; PASS, both module categories have enough injectives for the stated noncommutative rings, and forgetting scalar endomorphisms gives precisely the abelian inverse image.
- Step 2: checked all six cited statements against the localization definitions and the comparison-pullback isomorphism; PASS, only their abelian-sheaf and site-identification clauses are used. The projection/graph Hom bijection gives inverse image as slice restriction, so the comparison on W has the stated source and target; no module tensor-pullback clause or finite coefficient hypothesis enters.
- Step 3: checked 03FD's objectwise equality, the derived-injective-vanishing leaf (Mathlib/CategoryTheory/Abelian/RightDerived.lean:153-159), 03F3's localization, and the etale-site-localization-open node's actual all-etale-object statement; PASS, injectivity is used only in the module category. Evaluation is additive and kernel-preserving by sectionwise operations and kernels.
- Step 4: checked the complete statement of lem-cbc-abelian-etale-proetale-cohomology-comparison against 099W(1), with 03F3 and 03FD on the pro-etale site; PASS, W is an arbitrary scheme, F restricted to W is an arbitrary abelian sheaf, and all coefficient restrictions are absent. Independent traversal found closures of 532 and 135 nodes for the abelian comparison and 03FD respectively, no cycles or missing nodes, and neither closure contains this item, sk-prop-sf-comparison, or sk-lem-pe-injective-acyclicity.
- Step 5: checked the four cited definitions against the injective-resolution computation and the sectionwise-kernel/sheafified-cokernel description; PASS after making additivity and left exactness of module direct image explicit. Exactness of J(W) in degree q means J^(q-1)(W) surjects onto the sectionwise kernel in J^q(W); its sectionwise cokernel is zero, and so is its sheafification. This verifies the elementary sheaf-exactness passage in every q > 0.
- New nodes: none; B1-B7 and the per-new-node duplicate/Mathlib-leaf audit have no new objects to check. Existing localization, abelian comparison and coefficient-change nodes supply the non-elementary inputs; no restatement of the item was created.

Small cases checked: the empty scheme and the zero ring give zero module cohomology; over a point the argument reduces to the same injective-resolution calculation. Coefficients F_p explicitly test the failure of the tempting underlying-injectivity shortcut, since its injective module F_p is not an injective abelian group. Matrix rings test the left-module/noncommutative convention. Degree 1 uses the image of J^0 in the kernel in J^1 exactly as in every larger degree. Degree zero is not claimed to vanish, and no affineness or quasi-compactness is needed.

I independently searched slopmaster2 by the item id, its recorded declaration, and comparison/acyclicity terminology. The recorded rightAcyclic_comparisonUpperStar_obj_of_injective still has a literal sorry at LowerStarAcyclic.lean:107-111, so it cannot close this item. My additional logged LeanFinder query used the more general vocabulary of morphisms of sites and preserved abelian cohomology; it returned generic injective vanishing, Grothendieck-category and locally injective morphism facts, with no matching theorem. A logged grep for proetale, ProEtale and rightAcyclic in Mathlib/CategoryTheory/Sites returned zero hits. I read the generic derived-vanishing declaration above: it requires the actual functor input to be injective, so it does not close this comparison-pullback item. Earlier actual search records are preserved.

Changes: added the elementary justification that module direct image is additive and preserves kernels, so step 5 satisfies the hypotheses of the cited right-derived-functor definition. Added this independent reading and its fresh search evidence. The statement, source route, five-step structure, dependency lists and all 19 verbatim citation records are preserved. No new node, Mathlib leaf, Lean file, compiler invocation, live-project edit, or manual git command was introduced. The original worker's Review by Q41 remains intact; its final handoff is completed by this second reader's delivery below.

Validation: the required unmodified deliver.py Q41 lem-pe-comparison-injective-left-modules-acyclic --no-push completed with OK (not pushed) at 76044d54fe: preflight passed. The trailing dot shown in the brief is not accepted by this installed tool; its documented two positional arguments were used. No preflight failure remained.
