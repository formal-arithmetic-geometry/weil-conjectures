# Q33 stage-1 report: lem-sf-cochain-tensor-model-rigidity

## Files written

- `dag/nodes/sec-six-functors/lem-sf-cochain-tensor-model-rigidity.json`: statement, split into four proof steps; not a Mathlib leaf.
- `citations.json`: nine verbatim excerpts, covering every node cited by every proof step.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. The sandbox initially contained only dispatcher brief markers, with no earlier split, report, or search log. The item's existing source, citations, and seven historical Mathlib searches were retained. Seven actual Q33 searches were appended from `searches.jsonl` after reading their results.

## Attachments

None. Searches for the exact blueprint tag and cochain/tensor/rigidity concepts in `lean/WeilConjectures/` found no declaration stating all the clauses. The existing `Sheaf.Paper.WeilTensorProduct` file contains the scheme-specific `AlgebraicGeometry.Scheme.wfTensorRepresentative_exists` and private formal comparison helpers. Its pro-etale completed coefficient specialization does not state this arbitrary ringed-site theorem with full faithfulness for every target category, and it is not a project declaration under `WeilConjectures/` eligible for the requested attachment.

## WANTED

None. All sources needed here are available locally.

## Defects and changes

No statement dispute. All hypotheses and all clauses of the item are unchanged. The original node had no proof. The essential distinction is between cochain representatives and homotopy representatives: the existing descent theorem gives full faithfulness only for the latter. It is not enough simply to cite that theorem as if the domains coincided. Step 1 proves the necessary quotient restriction argument explicitly. Likewise the representative isomorphism has to use the canonical factorization on its source and inversely on each target input; Step 3 spells out the composite.

The chapter record and `sk-rem-sf-pf-done` unit were read. The unit records that the projection-formula interface is discharged and has no proof steps of its own. This item is a foundational tool below the first K-flat tensor computation sentence of `def-wf-tensor-product`; it changes no chapter or unit route. The item is not a unit key node. `coord/dag-sync.md`, requested by the inherited isolated-run appendix, is absent in this live read clone; the direct-delivery brief supplies the active live-repository protocol.

## Not duplicates

No new node pairs: none were created. Whole-DAG searches for fully faithful precomposition, localization, homotopy quotient and K-flat representative descent led to reuse of `lem-weil-pbc-site-derived-tensor-descent`. Blueprint searches with `tools/blueprint_refs.py search` for `K-flat`, `localization`, `precomposition`, `tensor model`, `homotopy category`, and `derived tensor product` found no blueprint node stating the full cochain comparison plus normalized uniqueness and arbitrary-target full faithfulness. `def-wf-tensor-product` is the precise blueprint ancestor. The generic quotient argument and lifting an inverse are short proof steps, not new nodes. The existing homotopy descent theorem is used as an off-unit generic tool, declared in `split_report.tool_uses`.

## Mathlib searches and source reading

The seven Q33 commands are recorded exactly in `searches.jsonl` and in the item's appended `mathlib_searches`. Both natural-language phrasings, both Loogle patterns, LeanSearch, and both grep patterns were read. All services answered; none is reported unavailable. `CategoryTheory.Localization.fullyFaithfulWhiskeringLeft` (Mathlib/CategoryTheory/Localization/Predicate.lean:278) gives the generic localization result, already represented by the existing localization-universal-property node. It does not supply the required restriction to flat-term K-flat representatives. `CategoryTheory.Functor.leftDerivedUnique` (Mathlib/CategoryTheory/Functor/Derived/LeftDerived.lean:136) assumes already given universal derived-functor structures, and so does not state this item. The two `mapDerivedCategoryFactors` forms concern exact functors between abelian categories and their induced derived functors, not the present representative tensor model. The flat-module exactness, ordinary module tensor extensionality, and constructor/no-confusion hits likewise do not state it. Therefore the item is not a one-line specialization of these hits.

Read `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean:94-118` for `Q`, `Qh`, and `quotientCompQhIso`, and the project's tensor differential description in `WeilConjectures/Mathlib/Algebra/Homology/Monoidal.lean`. No Lean was written and no compiler, Lake, or build was run.

## Review by Q33

I read the item's source, the first sentence of `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/def-wf-tensor-product.md`, and the old live representative argument in `lean/Sheaf/Paper/WeilTensorProduct.lean:690-769`. For the underlying literature I read Stacks 013H (`derived.tex`, `definition-complexes-notation`, especially clause (5)) and 06YS, 06YT, 06YU (`sites-cohomology.tex`, `lemma-K-flat-resolution`, `lemma-derived-tor-quasi-isomorphism-other-side`, `definition-derived-tor` and the construction immediately before it). There are no new node sources to audit. The proof is marked agent-written because its explicit quotient and transformation argument makes precise these literature constructions rather than copying a printed theorem verbatim. It uses no SGA source.

For Step 1 I opened the complete statement of `lem-weil-pbc-site-derived-tensor-descent`, and checked that its representative category consists of K-flat complexes with flat terms on an arbitrary site small relative to the module universe. I opened `def-pc-kflat-complex` and `def-pc-flat-sheaf-modules`: the former tests acyclicity after total tensor with every acyclic complex, and the latter requires exactness of sheaf tensoring. These are exactly the item's conditions. Thus the two representative categories have the same complexes as objects, with chain maps on one side and homotopy classes on the other. The proof of full faithfulness of quotient restriction is componentwise: every morphism pair has representatives, so its naturality square is already the square for the representatives, while the component family is unchanged. This proves a short fact from the quotient definition, not a hidden resolution or localization lemma. In particular it never incorrectly treats the quotient itself as faithful.

For Step 2 I checked that the final sentence of the existing homotopy descent node gives both existence and uniqueness of extensions of arbitrary natural transformations for every category E. This is stronger than invertible transformations and is exactly what the step uses. Both variables are present in that sentence. I also opened `def-weil-abstract-derived-category`, which identifies the cochain and homotopy localizations, and checked the explicit canonical factorization in Mathlib's `quotientCompQhIso`. Conjugation by this natural isomorphism identifies the two restriction transformation sets. No small-index colimit assertion, boundedness assumption, projectivity, field coefficients, or functorial resolution hypothesis is introduced.

For Step 3 I checked the same descent node's natural tensor comparison clause and its reference to the total tensor defined by `def-pc-tensor-complex-sheaves`. I read that definition's full signed direct-sum formula, and the full statement of `def-pur-sheaf-tensor-product`, which defines the tensor as sheafification of the sectionwise balanced tensor. The source and target factorization isomorphisms in the displayed composite have the correct directions: Q to Qh after the quotient at the tensor output, and its inverse at the two inputs after applying T. Whiskering the given homotopy comparison is enough; no closure of representative objects under an auxiliary construction, change of tensor, or transport between different flatness notions is used. I kept the same predicates literally, rather than assuming an unstated comparison between independent encodings.

For Step 4 the only inputs are the established Step 2 and the supplied isomorphisms r and rprime. I checked the types of rprime composed with inverse r and of its inverse. Fullness lifts them both; faithfulness makes the lifted composites identities. Cancellation of r gives uniqueness with exactly the prescribed normalization. This verifies an isomorphism of bifunctors, not merely objectwise isomorphisms. No further cited theorem is required and no new node restates a conclusion clause.

I checked the delivery-errors B--E requirements against these files. All non-elementary external facts are in the statements of the cited existing nodes; nine citation excerpts were checked as literal substrings. New-node source, statement-only, and same-tag duplication rules are vacuous because none is created. All four proof steps are below 2000 characters (1131, 875, 1112, 998), and none conceals a separate comparison lemma or an unproved standard assertion. The statement has the required category, ring, universe and representative hypotheses. Small cases checked: zero ring and empty site (all constructions become trivial and still typed), the one-object site over a field (all terms flat; homotopy classes remain necessary), and arbitrary unbounded complexes (the proof uses the existing unbounded descent statement and never assumes boundedness). Over the one-object Z-site, Z/2 concentrated in degree zero is not mistakenly declared a flat-term representative; the argument concerns only the stated full subcategory. None of these cases yields a counterexample. The proof needs no functorial choice of K-flat resolutions.

## Unfinished work

None in the stage-1 split. Existing dependency nodes retain their own implementation/proof obligations. Server dry-run and direct delivery are the remaining mechanical actions of this report's preparation.
