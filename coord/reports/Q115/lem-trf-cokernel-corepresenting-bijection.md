## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-cokernel-corepresenting-bijection.json (statement item, split into four explicit elementary steps; no exact Mathlib match). Supporting sandbox files: citations.json, report.md, and the search command's searches.jsonl. No new nodes and no Mathlib leaves created.

Attachments: none. I searched lean/WeilConjectures for the blueprint id, corepresenting/corepresent and cokernel-bijection terminology. The project hits concern sheaf generators, Ext comparison and specific cokernel maps, not this arbitrary pair of compatible Hom bijections; there is no exact project attachment. Nothing was written to Lean, compiled, or built.

WANTED: none.

The imported statement is correct and unchanged. Its absent proof is replaced with the argument behind the last display of Stacks Tag 0793. There is no need to assert additivity or zero preservation of R: zero preservation of theta_2 is an explicit hypothesis and is used at exactly the necessary points. No source dispute was found. The inherited long blueprint ancestry is retained; the latest ancestor and unit were read without modifying their route.

Nothing remains unfinished in this one-level split. The pre-existing searches and provenance are retained, and new real searches are appended from this item's log. No search was invented.

## Searches and reuse

I searched the entire DAG for Tag 0793, corepresenting and cokernel/universal-property terminology, and ran tools/blueprint_refs.py search for corepresent, Hom bijection, partially-defined, and cokernel, as well as ancestor for this item. There is no equivalent blueprint node: Hom-bijection hits concern adjunctions in geometric settings; cokernel hits include the abelian-category definition and specialized sheaf/module results. The existing def-weil-pbc-category-colimit gives the universal factorization for a finite parallel pair, which is all the proof needs. No new duplicate is created.

Mathlib searches ran through the required msearch.py command: LeanSearch, Loogle, grep and two different LeanFinder phrasings, with exact queries/results in mathlib_searches and searches.jsonl. The namespace-only Loogle query was unrecognized and is not treated as evidence of mathematical absence. I read PartialAdjoint.lean:149-193: corepresentableByCompCoyonedaObjOfIsColimit constructs the Hom equivalence from the library-chosen partial adjoint and an entire colimit diagram, rather than the supplied L_i, theta_i, D and arbitrary c with the specified formula. Identifying those choices is additional work. I read Limits/Shapes/Kernels.lean:585-663, 807-850 and 885-914: desc, its factorization and uniqueness, map and mapIso are single-category cokernel operations, not the cross-category theorem here. Equalizer-preservation hits concern applying a functor preserving an equalizer, not the given Hom bijections. The present direct universal-property proof avoids extra comparison nodes.

## Not duplicates

No new nodes. The item is not the existing lem-trf-partially-defined-module-adjoint (existence of a left adjoint on all objects), nor lem-trf-partial-adjoint-generator-presentation (construction of presentations). Those supply other parts of Tag 0793. The item assumes the presentations and compatible bijections and proves their normalized cokernel Hom comparison. def-sp-abelian and def-weil-pbc-category-colimit are reused without modification.

## Review by Q115

I read Stacks homology.tex, lemma-partially-defined-adjoint (Tag 0793), especially its final paragraph at lines 7442-7463: the two presentation sequences and the three displayed Hom identifications. The item makes that argument's maps and naturality explicit. Unlike a proof that speaks of kernels of abelian groups without justification, this proof only uses pointed-set bijections and their stated compatibility; no unstated additive structure on theta_i is required. For the existing definitions I read the statements of def-sp-abelian and def-weil-pbc-category-colimit in full. The former supplies the preadditive setting and cokernels; the latter explicitly supplies a unique factorization through a colimit. The finite walking parallel pair is small, and its two arrows are D and zero, or d and zero. Its cocone condition says precisely that a map kills D or d. Thus the cited definition really gives the uniqueness used, without any large-index existence assertion.

Step 1 cites def-sp-abelian and def-weil-pbc-category-colimit. It explains the coequalizer interpretation, checks theta_1(vc)d = theta_2(vcD) = theta_2(0) = 0 using cD = 0, and factors through the given q. This is a direct instance of the universal property, not a new general preservation theorem. The map is characterized by exactly the equation in the item.

Step 2 cites the same colimit definition for c. I checked every arrow's domain: bq has source P_1 and target R(X), its theta_1 inverse has source L_1, and precomposition with D has source L_2. Compatibility and qd = 0 give theta_2(aD) = theta_2(0); injectivity gives aD = 0, and only then is c's factorization invoked. The inverse is precisely the formula asserted in the item.

Step 3 cites the colimit definition's uniqueness, first through c, then through q. The two displayed composite equalities are written explicitly using the inverse identities of theta_1. I did not cite an epimorphism lemma: uniqueness for the two given cokernels suffices, and no node's proof is used as though it were its statement.

Step 4 cites that definition's uniqueness for q after displaying both composites. The middle equality uses exactly the assumed target naturality of theta_1, with v c as input. A second use of uniqueness proves uniqueness of the whole family pointwise. No preservation of cokernels by R, adjunction theorem, Yoneda theorem, or extra non-elementary input is hidden in this step.

I checked delivery-errors B--E against the actual files. All objects are introduced in the unchanged item, the TeX is singly escaped in parsed JSON, and the source has a Stacks tag and label. There are no unsplit new nodes, hollow definitions, clause-restating nodes, or duplicate nodes. Every citation has a verbatim statement quote in citations.json. Every step is a short calculation from the supplied hypotheses and the cited definition; all four are elementary, and none exceeds 2000 characters. The proof dependencies equal the union of uses and are existing definition nodes, so there is no new route departure or cycle.

Small cases checked: if d = D = 0 and q = c = identity, the construction gives theta_1; if d = D = identity and their cokernels are zero, both Hom sets are singletons, since compatibility and theta_2's zero condition force theta_1^{-1}(0) = 0. Taking R the zero functor likewise produces singleton Hom sets under the hypotheses. These cases introduce no nonzero-object or nonempty-generator assumption. Arbitrary nonchosen cokernels work because only their universal properties are used. No mathematical statement correction was needed; the repair was to supply the missing proof and its explicit inverse/naturality checks.
