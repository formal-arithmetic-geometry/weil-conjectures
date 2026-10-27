# Stage-1 report: lem-trf-representable-sum-shriek-acyclic

## Files written

- dag/nodes/sec-trace-formula/lem-trf-representable-sum-shriek-acyclic.json: existing statement, now split into ten explicit steps; statement unchanged; Mathlib has component facts, not the whole assertion.
- citations.json: one verified verbatim statement excerpt for each step/node citation.
- report.md: this report. searches.jsonl is the unmodified output log of the authorized search command.

No new nodes and no new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures by the blueprint tag and representable/freeYoneda/Kan-acyclicity notions. The free-Yoneda generator and pullback declarations concern component statements, not the whole item. The nearby project module lean/Sheaf/CategoryTheory/DerivedColimitBar.lean contains the ancestor argument in its docstring and a sorry proof (line 511); it is not an attachment. The existing general derived-computation node is cited as a dependency, not claimed proved here.

## WANTED

None. All sources used are present locally.

## Findings and changes

The live item had an empty proof, and the sandbox contained no item or earlier report. I copied the current live node, retaining its statement, source, provenance, recorded searches and blueprint chain. There was no repair-note file. I added an assembly proof rather than moving the item's clauses into new nodes. The non-elementary projective-resolution and total-derived-computation input is already the statement of lem-trf-bounded-above-acyclic-derived-computation. Its current statement explicitly has both resolution existence with a prescribed bound and invertibility of the canonical comparison on bounded above projective complexes.

The arbitrary coefficient modules must not be assumed projective. For instance, with E the terminal category, R = Z and M = Z/2, L_U(M) is just the nonprojective module M. The proof instead resolves M first, forms sums of induced projective resolutions, and checks that both underived images of the augmented resolution are quasi-isomorphisms. Naturality then proves that the actual canonical comparison, not merely some isomorphism between the objects, is invertible. No preservation of infinite sums by a derived functor is assumed.

I read the chapter and sk-i-curve-zero unit records, the current main-20261015 local-term-locality source and the inherited blueprint chain. This item is a lower homological tool along the existing cotangent/derived-colimit branch, and does not replace a step of the chapter or unit route. I ran blueprint_refs.py ancestor and searches for projective, 08PG, left Kan, and representable sums. The generic projective-computation tool already exists in this same unit. No chapter/unit record is changed.

## Mathlib search results

I read all six new logged results in searches.jsonl, including both semantic phrasings, Loogle and both source greps. Loogle identifies CategoryTheory.Presheaf.freeYonedaHomEquiv. I read its definition and inverse at Mathlib/CategoryTheory/Generator/Presheaf.lean:46 and following; its formula is exactly the elementary adjunction checked in Step 3. The second grep finds ModuleCat.enoughProjectives at Mathlib/Algebra/Category/ModuleCat/Projective.lean:58; I read the free-module presentation there. LeanFinder finds module-presheaf colimits, the free-presheaf adjunction, and ModuleCat.projectiveResolution. LeanSearch finds ordinary Kan-extension colimit comparisons. None states the entire arbitrary-coefficient sum-acyclicity assertion, or yields it by a one-line specialization. The component facts have direct proofs in the elementary steps, so no new nodes are needed for them. I retained the inherited Q94 searches separately; the new records reproduce exactly the tool/query entries actually executed by Q21. All six new calls succeeded; no outage is recorded as absence.

## Not duplicates

There are no new nodes, hence no new/existing same-tag pairs to justify. The whole-DAG 08PG search found the existing derived-colimit family, including this item and its ancestor. I reuse the general bounded-above computation node rather than duplicate its projective-resolution or canonical-comparison clauses. No descendant of the item is cited.

## Review by Q21

I read Stacks sites-cohomology.tex, Tag 08PG (example-left-derived-colimits), including its representable-generator calculation and its warning that homotopy verifications are omitted. This proof uses the projective-resolution refinement already named in the item's source, not that omitted simplicial verification. I also read derived.tex at Tag 0646 (lemma-projective-resolutions-exist) and Tag 06XN (lemma-find-existence-computes). The existing derived-computation node packages the needed bounded-above theorem under the everywhere-defined comparison hypothesis; I read its entire statement. The arbitrary-coefficient details below are written by me, so proof_origin.by is agent, with the Stacks place and refinement identified. No SGA source is used. No new-node source requires review because there are no new nodes.

For Step 1, I read the statements of def-weil-pbc-sites-and-cohomology, def-weil-sheaf-of-modules-category and def-weil-pbc-direct-sum-modules. The first gives the equalizer sheaf condition, which is tautological on identity covers. The second states exactly the sectionwise kernel and sheafified-sectionwise cokernel rules and abelianness under the size hypothesis. Sheafification is the identity here. The third describes finite-support families and their componentwise operations, from which the coproduct universal property is explicitly checked. E and D are small in the working module universe; this remains true for the index pairs (U,x). Modules themselves are the one-object case. No general-site sectionwise epimorphism assertion is imported.

For Step 2, the cited direct-sum definition explicitly expresses each element as a finite sum of its components. I used it to prove injectivity, exactness in the middle and surjectivity of sums by finite-support lifts. The projectivity argument separately chooses a lift on every projective summand and takes their universal map. This works for infinite and empty sums. These are elementary arguments, not an uncited theorem about arbitrary Grothendieck categories.

For Step 3, no external theorem is used. Both directions of the evaluation bijection are written down, with the naturality and inverse checks on every generator. The variance is contravariant: restriction by b takes (a,m) to (ab,m), and H(b)H(a)=H(ab). The identity arrow supplies the inverse check. This is also the formula read in Mathlib, but the step proves it directly.

For Step 4, exactness follows by applying Step 2 to the fixed Hom(V,U) index set. Projectivity is proved by lifting P -> H'(U) across the pointwise surjection H(U) -> H'(U), and translating the lift back through Step 3. Evaluation therefore has precisely the epimorphism-preservation property this lifting argument needs.

For Step 5, R is projective because a linear map out of R is determined by 1. The free presentation on all elements gives enough module projectives without any finite-generation or freeness hypothesis on M. The specified presheaf presentation is natural by Step 3, has projective source by Steps 2 and 4, and is epic because (V,y,id_V,1) maps to y. I checked that the coefficient formula is r H(a)x, as in the unchanged statement.

For Step 6, I read def-weil-pbc-category-colimit: its statement gives exactly the unique-factorization universal property used here. Every cocone map on (a,m) equals its value on (id_U,m), since the diagram is over E^op. Thus the cocone with value M is universal. This also verifies that the coefficient map is the identity and that the isomorphism commutes with module maps; this last check matters for the differentials in Step 9.

For Step 7, the left-Kan adjunction is part of the item's hypothesis. I constructed the two maps with its unit and Step 3; I checked both composites rather than quoting a full-faithfulness-only Yoneda result. Naturality of the unit makes the composite on A equal to the unit on every (a,m). The other composite is the identity on the distinguished identity summand, which Step 3 detects. No faithfulness, full faithfulness or exactness of u is required.

For Step 8, the same colimit-definition statement gives the colimit/constant adjunction. The proof explicitly transfers the coproduct and cokernel universal properties through each adjunction. Preserving zero and finite biproducts then preserves the diagonal/codiagonal formula for addition, so the functors are additive as well as right exact. This checks the precise hypotheses of the cited derived-computation node, including for an arbitrary small sum T.

For Step 9, the quote from lem-trf-bounded-above-acyclic-derived-computation states the existence of a projective resolution with the same upper bound. Its hypothesis enough projectives was proved in Step 5 and abelianness in Step 1. Taking bound 0 gives the required module resolutions; the argument also applies to any family of resolutions supplied in the statement. The image descriptions are the natural, coefficient-preserving isomorphisms of Steps 6 and 7, hence identify the actual differentials and augmentations, not just the terms. Exactness of the sums and L_U from Steps 2 and 4 proves all three augmented complexes are resolutions. Every term of the presheaf resolution is projective, although the resolved modules need not be.

For Step 10, I checked the projective-computation quote against the same node's statement: it says epsilon_P is an isomorphism for every bounded above projective complex. The item's everywhere-defined total-derived hypothesis is exactly retained; no derived existence is deduced from enough projectives alone. I also read def-weil-abstract-derived-category, whose localization clause says quasi-isomorphisms are inverted. The naturality equation therefore has three invertible factors and proves epsilon_T itself invertible. On D the same argument applies to the indexed family (uU_c,M_c), proving the further acyclicity of u_!T.

I checked small cases: E empty (only the zero presheaf and empty sums), zero ring, zero module, empty indexing set, E terminal and M nonprojective, repeated/non-distinct U_c, and a nonfaithful u. None needs a new hypothesis. In the terminal case the comparison reduces to the identity functor computed by a projective module resolution. All ten steps are shorter than 2000 characters; there is no long step hiding a separate comparison lemma. Every cited statement excerpt in citations.json was tested as a verbatim substring of the current cited statement. The only non-elementary steps, 9 and 10, cite the actual existing homological theorem. I checked B--E of delivery-errors.md against the files: no new standalone nodes, clause relabelling, uncited source theorems, false sectionwise claim on a nontrivial topology, extra projectivity assumption, or source/route substitution remains.

## Unfinished work

None in this one-level split. General derived-computation dependencies keep their own independent DAG state. Delivery checks are reported below after the required remote dry run.

## Delivery checks

The first remote dry run rejected the phrase “The item's hypothesis” in Step 10 under the standalone-statement wording gate. I replaced it with an explicit reference to the assumed total left derived functor being defined at every complex with its canonical comparison. No mathematical hypothesis or conclusion changed.
