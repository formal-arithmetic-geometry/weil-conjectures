# Stage-1 report: lem-sf-cbc-diagonal-resolving-complexes

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-cbc-diagonal-resolving-complexes.json: existing statement, now split into seven steps; no Mathlib match for the complete assertion.
- citations.json: one verbatim statement quotation for every node cited by every proof step.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The sandbox also contains searches.jsonl, produced by the required search command, and write_split.py, the sandbox-only JSON-writing helper.

## Attachments

None. I searched the live project's WeilConjectures source for the exact blueprint tag, the item id, constant/diagonal diagrams, and K-flatness terminology. The exact tag has no hit. The existing K-flat constructions in FromJoel/CategoryTheory/Abelian/Flat/KFlat.lean, and the module-sheaf flatness, reduction and base-change files, do not give all the diagram-site assertions with the specified evaluated total-tensor normalization. No sorry declaration was counted as a finished proof.

## Wanted sources

None. All sources used are present in the read-only literature directory. This is an agent proof assembling existing results, and is recorded as such.

## Corrections and source audit

The statement is unchanged, including arbitrary small J, unbounded cochain complexes, a nonconstant sheaf of rings R, and the conditional localized-site/extended-complex application. There is no statement dispute. The imported reference to 06YS is background about resolutions; a resolution-existence theorem is unnecessary here because P is already assumed K-flat with flat terms. The proof instead uses the definition at sites-cohomology.tex, Tag 06YN (definition-K-flat), which I read directly, and the normalized algebraic inverse-image tensor comparison sourced by Tag 03EL (sites-modules.tex, lemma-tensor-product-pullback). I also read the sheaf-tensor construction and bilinear characterization preceding 03EL, and the explicit total convention recorded in def-pc-tensor-complex-sheaves (homology.tex, 012Z, and sites-cohomology.tex, 06YL).

Removed def-weil-abstract-derived-category from stmt_deps: the item states an ordinary cochain isomorphism and K-flatness, not an isomorphism of derived objects, and that definition is not a direct notion in its statement. It remains available through the existing cohomology theorem's own dependencies. All other inherited fields, original searches and blueprint ancestry are retained.

The chapter and unit records were read. The item is not the unit's key statement, so no unit file changes. The current main-20261015 fix-lem-exchanges.proof.md places this ingredient under Steps 1–2, construction of the open comparison and coefficient naturality. The proof supplies that ingredient without changing the coefficient route or using SGA. The two off-unit generic tools (diagram-site realization and normalized inverse-image tensor comparison) are declared in split_report.tool_uses. The exact-cohomology node is already a Mathlib leaf.

## Unfinished work

None at stage 1. Existing cited nodes retain their own states; this split makes no assertion that all their Lean proofs are closed.

## Not duplicates

No new nodes were created. I searched the DAG and whole imported blueprint for diagram/evaluation tensors, K-flatness and constant diagrams, including blueprint_refs.py search and ancestor. The searches led to existing general tools rather than a new lemma or a node restating one clause of this item. No blueprint node states the full item in another form, so same_as stays [].

## Mathlib searches

All additional searches were run with batch2/msearch.py O3 lem-sf-cbc-diagonal-resolving-complexes and copied from its actual log, preserving the inherited history. LeanFinder was run with two different phrasings; Loogle used the IsKFlat/Functor pattern; grep searched K-flat terminology together with constant/diagonal/evaluation, and then IsKFlat/KFlat in Algebra/Homology. LeanSearch returned complex tensor constructors, evaluation preservation and ordinary flat-module exactness. I read the tensorObj/HasTensor/tensorHom source in Algebra/Homology/Monoidal.lean: it defines the total construction and does not prove the module-sheaf diagram assertion. The LeanFinder hits concern representably flat functors, ordinary flat modules, condensed exact colimits and condensed monoidal structures. None gives the full item or a one-line specialization of it. No unperformed search was recorded, and no service failure was reported as absence.

## Review by O3

I checked this split as its author against delivery-errors B through E, with the item and the cited statements open. There are no new unsplit nodes to audit for B1/B2; all new mathematical work is in the item's proof, not a statement-only restatement of its clauses. For B3/B4/B7 I checked that the notions are already defined by the cited module, tensor, K-flat and flatness nodes, that the mathematical text uses single-escaped TeX after JSON decoding, and that no tag supplies an unstated meaning. For B5/B9 I verified the Stacks labels in the local source, kept the exact blueprint ancestor and intermediate chain, and recorded the current blueprint role. For B6/B8/B10 there is no new leaf or attachment; the whole-item searches do not justify either.

Step 1 uses the statement of lem-weil-pbc-diagram-site-realization for its exact component evaluations and its equivalence with Fun(J,Mod(R)); I did not take a tensor or coproduct claim from that statement. It uses lem-weil-pbc-exact-functor-complex-cohomology for the explicit natural comparison H^n(e_jB) ≅ e_jH^n(B). Both categories are abelian by the module-category setup, and evaluation is additive and preserves finite limits and colimits as required. Joint detection of zero is proved by the explicit inverse transformations to the zero diagram. Detection of exactness is then obtained from the three-term complex, not asserted as an extra property of a definition.

Step 2 uses only the diagram equivalence and existence of the module sums recorded in def-pc-tensor-complex-sheaves. I wrote the transition maps, identity/composition check and universal factorization into an arbitrary diagram N. This is a routine coproduct universal-property argument, not a hidden colimit theorem. It proves preservation for all small families, including the countably infinite degree diagonals needed for unbounded complexes; no finite-support assertion about all global sections of a sheafified sum is used.

Step 3 uses the same diagram-site realization for the set-sheaf geometric inverse image, its adjunction and finite-limit preservation. The statement def-weil-pbc-algebraic-inverse-image specifies exactly the algebraic operation transport; for evaluation these operations are component operations, so all its graph conditions are identities. The existing lem-weil-pbc-algebraic-inverse-image-tensor-comparison states both the natural tensor isomorphism and its forward pure-section formula. The cited def-weil-pbc-ringed-tensor-section-calculus identifies the actual pairings and supplies their naturality and extensionality. The coefficient ring is identified as e_j(Delta R)=R, with no field or constant-on-C hypothesis.

Step 4 uses the actual direct-sum total differential of def-pc-tensor-complex-sheaves, and the two-variable naturality of the existing tensor comparison. I checked both differential terms separately: d_A tensor 1 and (-1)^r times 1 tensor d_P. Evaluation is additive; the degree r and summand order are unchanged. This proves a cochain isomorphism rather than merely degreewise isomorphisms or an unnamed derived identification. Step 5 checks simultaneous naturality by each coproduct inclusion. Its sheafified pure-section formula follows from the existing normalized tensor comparison and actual pure pairing. I did not replace a canonical map by an arbitrary isomorphism.

Step 6 uses def-pc-flat-sheaf-modules for its exact-functor definition, not merely the word flat. It applies the given flatness of P^i to the evaluated short exact sequence, uses Step 3's natural comparison on every arrow, and invokes Step 1's proved detection of exactness. The argument proves the whole tensor functor is exact, not just injectivity on one sequence. Step 7 uses the acyclic-complex quantifier of def-pc-kflat-complex, the exact cohomology comparison and the cochain isomorphism already constructed. The test complex A is arbitrary and may be unbounded. No flat-term assumption is incorrectly substituted for K-flatness.

For C1/C4, every non-elementary tool used above has an existing node citation whose statement I read; citations.json quotes its verbatim statement for each occurrence. Source references alone carry no unlisted theorem. For D1–D5, none of the conclusion has been moved into a new lemma, no source's omitted proof is waved away, and no resolution, derived descent or tensor conservativity is assumed. The dependency direction of each tool is left for the mandatory server DAG check as well as this source review. For E1–E7, I verified the actual ringed sites, variance J^op x C giving covariant J-diagrams, the coefficient equality, the direction of the forward normalized tensor map, all exactness hypotheses, and both naturality variables.

I tested J empty (the diagram category is the zero category and detection is vacuous but valid), J a singleton (the comparison is the ordinary identity), a category with a nontrivial arrow (all transitions commute by tensor naturality), zero complexes and the zero ring. For genuinely unbounded complexes the sums indexed by r+s=n remain countable and the sign check is unchanged. The final localized-site/extended-complex sentence is conditional on the same K-flatness and flat-term hypotheses; it does not assert that an arbitrary extension preserves them. Every proof step is below 2000 characters, and the coproduct and sign calculations are explicit routine arguments. No Lean file, compiler, Lake tool, repository file, launcher file or git command was used for a mutation.
