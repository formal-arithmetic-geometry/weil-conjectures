# Q160 stage-1 report: lem-sfb-multivariable-derived-calculus

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-multivariable-derived-calculus.json`: item split into seven steps; its statement is unchanged.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-product-localization.json`: statement-only Mathlib leaf, `CategoryTheory.Functor.IsLocalization.pi`, `Mathlib/CategoryTheory/Localization/Pi.lean:35`.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-unary-left-derived-calculus.json`: statement-only unary support node; project attachment candidates recorded, pending maintainer verification. No proof is deferred by copying the whole multivariable item into this node.
- `citations.json`: full verbatim statements for every node cited in each item step. `searches.jsonl` retains the earlier attempt's searches; their actual results were read and reused. No Lean was written and no compiler or Lake command was run.

## Attachments

`CategoryTheory.LocalizerMorphism.Derives.hasLeftDerivedFunctor` belongs to `lem-sfb-unary-left-derived-calculus` (existence clause), `WeilConjectures/FromJoel/CategoryTheory/Localization/DerivabilityStructure/Derives.lean:54`.

`CategoryTheory.LocalizerMorphism.Derives.isLeftDerivedFunctor_iff_isIso` belongs to `lem-sfb-unary-left-derived-calculus` (candidate criterion, including counit invertibility), the same file, line 107. Both sources were read with their ambient hypotheses. The archived `local/sorry_map_slopmaster2_full.jsonl.gz` records `s=false, ts=false` for both declarations. Mathlib's chosen total-left-derived functor, counit and its instance supply the selected pair; the IsLeftDerivedFunctor/right Kan extension interface is exactly the displayed natural-transformation bijection. These are `lean_candidates`, not a worker-assigned closed audit.

There is no declaration giving the whole multivariable item. Searches for the item tag, product derivability and left derived functors under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found useful general support declarations, but no single exact attachment giving all the item's clauses. Master's sorry declarations were not used as proof evidence.

## WANTED

None. This is an agent-written expansion of the current blueprint's categorical descent argument. No SGA source is used.

## What was wrong and what changed

The retained sandbox already contained a split, report, citations and search log. I retained their mathematical route and all logged searches, compared the item with the current shared repository, and ran `deliver.py --no-push` before making repairs. That command exited with five diagnostics: both new statements lacked explicit definition references and used Unicode mathematics, and the product leaf lacked its verified line number. Those are repaired by TeX statements, explicit category/localization/derivability references, and Pi.lean:35.

Reading the proof uncovered additional mathematical faults. The old comparison step applied the universal property of LF, although its desired target is LG; it also wrote the ill-typed composite L followed in ordinary mathematical composition by LF. Step 5 now applies LG's universal property to V=LF and the well-typed transformation tau composed with epsilon. The last step previously passed only from y to L(a), without ever reaching a resolving object. Step 7 now chooses a resolution P to a, uses that L inverts its arrow, and writes the naturality equation and cancellation explicitly. The old identity-inclusion argument incorrectly called its comma comparison the identity; step 3 instead exhibits a terminal object in every relevant triple category. Finally, product localization now precedes product derivability, and is applied also to the resolving subcategories' localizations.

## Statement corrected

STATEMENT-DISPUTED: the earlier sandbox's *new unary support node* wrote epsilon from `L composed with LF` to F, using ordinary composition with L:A to D and LF:D to H. That order is ill-typed: LF must be applied after L. Its corrected TeX is epsilon:LF composed with L to F, agreeing with its own universal-bijection formula, the item, and the source's Lean `L ⋙ LF ⟶ F`. This is a typing repair to an undelivered support node, not a change to the imported item's statement or hypotheses.

## Not duplicates

lem-sfb-product-localization vs lem-coef-dg-product-localization: the new node concerns ordinary category localizations at arbitrary arrow classes; the existing node concerns dg categories, dg nerves and infinity localizations. The latter does not state the ordinary finite-index localization theorem.

lem-sfb-unary-left-derived-calculus vs def-sfb-left-derived-functor: the existing blueprint definition concerns additive functors on monoidal abelian categories and their K-flat resolutions; the new support statement is the general categorical existence and criterion for an arbitrary full left derivability inclusion, with no abelian or monoidal structure. Its general project declarations are already proved and reported for attachment.

lem-sfb-unary-left-derived-calculus vs lem-sc-nattrans-from-resolving-class: the latter constructs transformations from a resolving predicate under a right calculus of fractions; it neither constructs unary derived functors nor gives the counit criterion. Its extra calculus hypothesis is unavailable here.

I searched the whole DAG by statements and by `Derives.hasLeftDerivedFunctor`, `Derives.isLeftDerivedFunctor_iff_isIso`, `IsLocalization.pi`, product localization and resolving-subcategory terminology. Blueprint searches for `left derived`, `derivability` and `localization` found no general equivalent node. The blueprint ancestor command confirms `lem-sfb-derived-monoidal`, through the present item. Both new nodes carry that ancestry and precise descent places. The existing generic localization-essential-surjectivity leaf is reused, not recreated.

## What remains unfinished

Nothing in the item proof is left implicit for a later split. The two new nodes are statement-only as required: one is a Mathlib leaf, and the other carries already proved project attachment candidates for the maintainer to verify. They introduce no new axioms or data constructions.

## Review by Q160

I read the current chapter and unit records, `SETUP.md`'s three-level route, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B through E. The current source is `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`: the sentences on K-flat left derivability, tensor descent in two variables, iterated derived products in three and four variables, and descending constraints and coherence. The item expands these sentences to a generic categorical tool, and I have kept every clause, including 1 <= n <= 4, identity inclusions, the exact universal bijection, the candidate iff, all comparison equations and both uniqueness claims. No unit route or target statement was changed.

For the new product node I read Mathlib/CategoryTheory/Localization/Pi.lean:28-40, not merely a search hit. Its finite index, categories, ContainsIdentities and coordinate IsLocalization assumptions are exactly the node's assumptions, and its conclusion is localization at MorphismProperty.pi. The new unary node was checked against the project supplement Derives.lean:39-109: `Phi.Derives F` is precisely inversion on the full inclusion's inverse-image arrow class, existence is line 54, and the candidate criterion is line 107. The lemma takes arbitrary categories, so there is no hidden additive, boundedness, completeness or calculus-of-fractions assumption. I also read the opposite-derived-functor supplement used in its proof and checked the archived audit. The node has no proof or proof dependencies, no hollow definition, and a complete self-contained statement. Its typing repair is documented above.

Step 1 uses the product leaf's entire finite-index statement, once for the ambient categories and once for P_i. Inverse-image classes contain identities, so both applications satisfy the declaration's hypotheses. Step 2 uses exactly the resolution clause and the explicit nonempty-connected triple-category condition of `def-sfb-left-derivability-structure`. All equations are coordinatewise, and the finite zigzag construction is written out; no separate product-finality lemma is being assumed. Step 3 uses the same definition and directly constructs the terminal triple (X,id,b), proving the identity case without an unsupported identification of comparison functors. These are elementary deductions from that definition.

Step 4 uses the unary support statement's existence and criterion. Its inversion hypothesis is checked by factoring a tuple of weak arrows into one-coordinate arrows, so the other objects remain resolving at every factor. Step 5 uses that same node's universal bijection for G, with test functor LF; identities, composition and inverses are checked by the actual counit equation and uniqueness. Step 6 is the injectivity of the very same bijection. For each of these citations I copied the full statement, including all hypotheses and the exact clause used, into citations.json.

Step 7 uses the statement of the existing Mathlib leaf `lem-trf-localization-essentially-surjective`, read in full and checked against Mathlib/CategoryTheory/Localization/Predicate.lean:201-206. It asserts an image object isomorphic to each target object with no calculus hypothesis. The step then uses the derivability definition's resolution arrow; the localization definition says its image is invertible. The displayed naturality equation and cancellation complete equality at every object. Thus I have not cited a definition for an existence theorem or used any cited node's proof instead of its statement. The essential-surjectivity leaf is a generic Mathlib tool, so it needs no off-route tool-use declaration.

Small cases: n=1 recovers the unary result; n=2 gives ordinary binary localization; n=3 and n=4 use finitely many coordinate paths. Identity inclusions work for arbitrary W containing identities, without Ore hypotheses, by the terminal triple. If one ambient category is empty, resolutions force no contradiction and the corresponding product/localized categories have no objects, so the universal bijection and detection claims have their empty-domain meaning. A nonempty A_i cannot have empty P_i because the resolution clause requires an object of P_i. The old report's claim that n>=1 alone excluded empty P_i was therefore corrected. The product leaf even permits an empty index set; the item retains its nonempty range. The unary type check and the two missing-resolution/universal-property issues were corrected before delivery.

I read and reused all retained msearch results, including second phrasings for both new nodes. Results now quote the actual logged records; in particular the unary LeanSearch result had contained unrelated derivation hits and is no longer described as a successful exact match. The precise left-handed support is in the project supplement, not in the installed Mathlib. No unavailable service has been recorded as a negative result. There are no Stacks tags for these categorical interfaces, so no unrelated tag is supplied in place of their actual source. I checked each proof step's length: every step is below 2000 characters, and each argument is expanded rather than hiding a standard comparison lemma. No elementary fact was added as a new node.
