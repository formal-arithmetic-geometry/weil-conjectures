## Worker report

Item: lem-sf-derived-completed-tensor-bilinearity. Group: Q37. Stage 1 only, 2026-10-21.

### Files written

- dag/nodes/sec-six-functors/lem-sf-derived-completed-tensor-bilinearity.json: existing statement node, split into seven steps; not a Mathlib leaf.
- report.md and citations.json: report and a verbatim statement quotation for every step/dependency pair. searches.jsonl was produced by the required search command.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written and no compiler was run. The item statement is unchanged. Added statement dependencies for the existing additive-functor and linear-functor notions.

### Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag, wfRationalTensorHom, completionLinear, completed tensor and derived bilinearity found no declaration giving the whole assertion. WeilFrobenius.lean has a finite-coefficient etale degreewise pairing, and KFlatDerivedTensorComparison.lean has a scheme-module representative comparison; neither gives this ringed-site completion and raw rational Hom action. They are not attachments.

### WANTED

None. All sources used are available locally.

### Faults found and repairs

The item had an empty proof, rather than an accepted split. Its parent-location reference was stale: wfRationalTensorHom_exists is now current parent proof Step 3, not Step 7. Updated that reference without changing the statement or the coefficient convention. The blueprint's one-sentence tensor convention is not a proof of the completed rational morphism action; the seven steps provide it and are marked agent-written.

Checked the source tags against literature/stacks-project/tags/tags. The tensor-product universal property is 00CX (algebra.tex lemma-tensor-product), and the base-change definition is 05G4 (definition-base-change). The existing module-base-change leaf's source calls the latter 05G3; its mathematical statement is usable, but this delivery's own source uses the actual tag 05G4. Derived-category definition 05RU is definition-unbounded-derived-category. No other node was edited.

### Searches and reuse

Searched all DAG node titles/ids for bilinear, tensor/linear, reflective/linear and additive/linear localization, then opened the statements of every node actually cited. Ran tools/blueprint_refs.py ancestor on the item and full-blueprint searches for bilinear, linear and K-flat. No blueprint node states the whole assertion; same_as is empty. In particular lem-coef-completed-tensor-scalar-linearity is only a specialized integral-constructible assertion in one scalar variable, not this ambient ringed-site theorem. It is not used to replace the argument.

The two new natural-language phrasings, Loogle query, grep and LeanSearch below were run through msearch.py with Q37 and this item. The earlier Q20 search records in the copied item are retained, not represented as new Q37 executions.

1. leanfinder: The K-flat derived tensor of sheaves is bilinear over global scalars and remains bilinear after Koszul completion and scalar localization. Hits were ordinary presheaf tensor and module flatness theorems, not the assertion.
2. loogle: "functor_linear_iff". Exact ingredient CategoryTheory.Localization.functor_linear_iff, already represented by lem-sfb-linear-localization-descent.
3. grep: derived.*[Bb]ilinear|[Bb]ilinear.*derived|completionLinear|rationalTensorHom. No hits.
4. leansearch: Derived completed tensor product of module sheaves is additive and linear in each variable and extends to rationalized morphisms. Hits include tensorRight_additive, presheaf tensor, direct-sum tensor and ordinary Noetherian finite-module adic completion. None gives the specified unbounded derived reflector.
5. leanfinder: An additive localization of a linear category makes derived functors linear and a reflective full subcategory inherits a linear reflector from its universal unit. Hits give the generic linear-localization ingredients and derived linear instances, not the completed tensor assertion.

Read Mathlib/CategoryTheory/Localization/Linear.lean, especially linear/functor_linear at lines 38/41 and functor_linear_iff at 79 with its hypotheses; DerivedCategory/Linear.lean and Basic.lean at the additive localization instances; TensorProduct/Tower.lean at distribBaseChange and its pure-tensor formulas. Those support the already-existing Mathlib leaves used here. No absent-from-Mathlib conclusion was drawn after only one phrasing.

### Route and tool uses

This serves def-wf-tensor-product, first sentence, with the adic integral tensor followed by completion and raw scalar localization in its current parent Step 3. The unit sk-rem-sf-pf-done is an interface-discharge remark with no separate numbered proof steps. This is a node-level expansion; the chapter and unit were not changed. No SGA source is used.

The generic exact fixed K-flat tensor, site tensor descent, Koszul reflector and raw localized-category composition nodes are declared in split_report.tool_uses with their particular uses. They supply constructions already fixed in the item or generic linear-category laws, not a different six-functor route. The maintainer may accept those tool declarations; no top-level tool_uses field was written.

### What remains unfinished

Nothing in this one-level split: all seven steps have arguments and cited premises. Existing dependencies remain independent queue items where not already finished. No new queue item is introduced.

## Not duplicates

No new nodes. The existing broader localization and module-base-change leaves are reused instead of restated, and the reflector's linearity is a two-line injectivity argument rather than a new node.

## Review by Q37

I read the item and current def-wf-tensor-product statement and its proof Step 3 against literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/def-wf-tensor-product.md, first sentence. The ringed-site generality and chosen completion model are the present item's explicit expansion of that convention, not a claim that the one-sentence blueprint already proves the result. I then read Stacks sites-cohomology.tex lemma-K-flat-resolution (06YS), the construction preceding definition-derived-tor (06YU), and algebraization.tex lemma-derived-completion (099B) and lemma-derived-completion-koszul (0A0E). The reflector statement supplies precisely the natural universal unit used, not a linearity assertion assumed without proof. There are no new-node source claims to review.

For Step 1 I opened def-weil-sheaf-of-modules-category, def-pur-sheaf-tensor-product and def-pc-tensor-complex-sheaves. Their statements give restriction-compatible module morphisms, tensor as sheafification of sectionwise tensor, and the signed direct-sum total construction respectively. The displayed equality on pure tensors is an equality of presheaf maps before sheafification, so applying that functor gives the sheaf equality. Summands determine the total map even for unbounded complexes. No preservation of products or convergence is being assumed. This is a direct calculation, correctly marked elementary.

For Step 2 I opened def-weil-abstract-derived-category, lem-sfb-derived-localization-additive and lem-sfb-additive-localization-linear. The first identifies q as localization of complexes, the second explicitly says this same q is additive, and the third needs only preadditive categories, an additive localization and a linear source. The module-sheaf category is abelian in the chosen universe and D(R) is additive; Step 1 supplies source linearity. Thus all hypotheses hold and the conclusion gives q's scalar preservation, not merely existence of some unrelated linear category. This step is non-elementary and cites the exact leaf supplying it.

For Step 3 I opened the statements of lem-weil-pbc-kflat-fixed-tensor-triangulated, def-weil-triangulated-category, lem-sfb-linear-localization-descent and lem-weil-pbc-site-derived-tensor-descent. The first explicitly gives exact descended functors for both tensor orders with arbitrary unbounded variable complex, canonically identified with the specified tensor. Exact functors are additive by the second. The linear-localization leaf concludes scalar preservation under the given descent isomorphism, with q additive and linear from Step 2. The tensor-descent statement explicitly supplies the equivalence from localization of flat-term K-flat representatives, hence a representative up to isomorphism of every fixed object. It is not used to assert linearity by itself. Conjugation by T(e,1) or T(1,e) uses only bilinear composition. Both variables are accounted for, and there is no unproved functorial choice of replacements. Every non-elementary input is a cited statement, not material borrowed from its proof.

For Step 4 I opened def-weil-linear-category and lem-weil-pbc-ringed-koszul-completion-reflector. The complete subcategory is full, so its Hom modules and composition are inherited. The latter statement includes both naturality of eta and the bijection Hom(LX,E) to Hom(X,E) for every complete E. Taking E=LY makes the two displayed composites equal only when the original arrows are equal. That is exactly the injectivity required; no assertion that an arbitrary adjoint between unrelated linear categories must be linear is used. Both scalar and sum equations follow at once, so keeping this elementary argument inside the item avoids an unnecessary reflector-linearity node.

Step 5 composes the two proved functors; def-weil-linear-category gives the needed bilinearity of composition. Its intermediate object is B(M',N), so the formula B(1,g) after B(f,1) is well typed even for non-endomorphisms. This proves bilinearity of the simultaneous action from the fixed-variable results rather than confusing categorical product-linearity with separate linearity.

For Step 6 I opened def-weil-module-base-change and def-weil-linear-scalar-localization. Although the former has kind definition, it is a Mathlib leaf whose statement explicitly includes the unique bilinear base-change theorem; the quotation includes that assertion. It is not being cited merely as a definition of tensor. The latter uses Hom tensor S, with morphism factor first. The item uses scalar factor first; the proof explicitly inserts the canonical flip, so the formula uses the same module, not an unidentified alternative coefficient model. This theorem needs no injectivity of the original Hom map and no torsion-freeness.

For Step 7 I read all four clauses of lem-weil-linear-scalar-localization-category. Its first two clauses give exactly the composition and identity formulas used. The simultaneous-composition comparison is multilinear in four independent arrows, with matching source and target Hom modules, and the displayed pure-tensor calculation has the scalar product in the right order. Distribution over finite sums proves it for all elements, without a fraction equality criterion or cancellation assumption. The last fraction formula is simply substitution of inverse powers in S. This is an elementary check of the bifunctor laws after Step 6, not an uncited localization theorem.

I checked edge cases: the empty list of completion generators (the identity reflector), the unit ideal (the zero complete subcategory), zero complexes and zero maps, the zero coefficient ring, p=0 or nilpotent (S=0), p a unit (ordinary scalar extension), and torsion Hom groups (for example integral maps killed by p). Every equation survives; the proof never cancels p or assumes finite generation, Noetherianity, boundedness, exactness of infinite products, or existence of a functorial K-flat resolution. The finite list and site/universe hypotheses agree with both supplied ringed-site construction nodes. All dependency closures checked are independent of the item, so none creates a circular proof.

I checked delivery-errors B–E with the files and sources open. There are no new statements to conceal a clause of the item, no omitted new-node hypotheses, no new duplicate, and no unsplit child with a proof. The proof has seven short steps, all below 2000 characters. Definitions are used only for their stated constructions; exactness, linear descent and bilinear scalar extension have exact cited statements. Corrected the stale parent-step reference and the local source-tag/label references as described above. All sixteen step citations are copied verbatim from the corresponding node statements into citations.json. The required dry run is the final mechanical gate; its result is recorded after it exits.

Validation: the required deliver.py --no-push exited 0 and printed OK (not pushed) at 8a8dff0f4d9 on 2026-10-21; server preflight passed. This validation note is included in the final rerun before push.
