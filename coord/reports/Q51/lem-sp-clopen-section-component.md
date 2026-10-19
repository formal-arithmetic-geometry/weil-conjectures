# Q51 — lem-sp-clopen-section-component

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-clopen-section-component.json: statement item, split in eight steps; no Mathlib match for the whole item.
- citations.json: verbatim statement quotations for each step citation.
- searches.jsonl: six actual msearch queries and their results; preserved by the search command.

New nodes: 0. Mathlib leaves: 0. The statement is unchanged; stmt_deps additionally names the existing cochain-complex and acyclicity definitions used by its complex clauses.

## Attachments

None. Searched the read-only WeilConjectures source for the blueprint tag, clopen section terminology, and K-injective/adjunction operations. The clopen hits concern trace pairings and valuation topology; the derived-functor hits concern unrelated mapping bijections. No project declaration supplies the component equivalence and all unbounded/direct-image clauses.

## WANTED

None.

## What needed repair

The item was a statement-only child of lem-sp-fullcd-ambient-adjoint. Its cited blueprint source proves a bounded-below etale assertion; that assertion does not itself provide the required pro-etale product equivalence or unbounded K-injective insertion. I retained the source's route, constructed its inverse on sections, and wrote the unbounded null-homotopy argument, rather than treating preservation of degreewise injectives as preservation of arbitrary K-injectives. There was no saved split, report, search log or active delivery process when this resumed turn began.

The existing lem-weil-pbc-etale-sheaf-clopen-product was read and not cited: it concerns abelian sheaves on the etale site, not the module category on the pro-etale site. The nearby lem-weil-pbc-clopen-section-direct-image likewise supplies a bounded-below etale derived conclusion. Neither is silently generalized here.

## Not duplicates

No new nodes. Whole-blueprint searches for clopen, sheaves disjoint, and disjoint, and DAG keyword searches found the two etale nodes above, the localization node, and generic open extension tools. None states this whole pro-etale, unbounded item. There is no need to turn any clause of this item into a new node.

## Review by Q51

I read the current main-20261015 proof of lem-weil-pbc-clopen-section-direct-image, the chapter and sk-prop-sf-existence unit, and the ancestor cor-exc-base-change-open-immersion-general and its update. This item serves the ancestor's compactification/refinement component calculation; it does not discharge the FullCD or ambient-adjoint existence assertions. I also read Stacks proetale.tex Definition 09AE (definition-extension-zero), sites.tex Definition 00VM (definition-sheaf-sets), and derived.tex Definition 070H and the proof of Lemma 08BJ (lemma-adjoint-preserve-K-injectives). The proof_origin is agent because the blueprint is agent-written and I extend its etale bounded-below calculation, with the actual argument written here. No SGA source is used.

Step 1 uses the statements of the open-immersion base-change and weakly-etale base-change lemmas, respectively for the component opens and their membership in the small sites. The localization lemma explicitly includes open immersions, identifies the component sites with slices, and identifies restricted constant rings. The statement of sk-def-pe-site expressly says Zariski covers are pro-etale covers, so the two-open covering needs no uncited claim about clopen affines or idempotents. I corrected that unnecessary inline assertion during review. The size convention is inherited from the small-site definitions, and no new large index category is used.

Step 2 uses the actual sheaf equalizer formula in def-weil-pbc-sites-and-cohomology and the sectionwise module/morphism description of def-weil-sheaf-of-modules-category. The empty-cover axiom gives zero sections on the empty scheme; the cross overlaps are empty and the diagonal overlaps give identities. This proves the natural restriction bijection, including its module structure, directly.

Step 3 constructs G(M,N) on every site object, on restrictions, and on morphisms. The same site axiom supplies pullback covers; matching families then split into two matching families and glue uniquely. The localization statement supplies exactly the coefficient identification used for the action, not a theorem about product decompositions. Restricting G and the step-2 map explicitly gives both inverse natural isomorphisms. This is the actual proof of the product clause, not an application of a new node restating it.

Step 4 uses prop-weil-pbc-proetale-constant-exact only for its stated exactness of inverse image with constant finite coefficients. Its finite discrete coefficient assumption holds for the finite commutative A here. On each open, the localization identification makes this inverse image ordinary restriction. Reflection of exactness is written as the two universal factorizations for kernels and cokernels in the product, so no unsupported assertion of sectionwise exactness is made.

Step 5 reads lem-weil-extension-by-zero-adjunction literally: the specific extension by zero of def-weil-extension-by-zero is left adjoint to restriction on pro-etale module sheaves. The insertion has the same Hom formula, and the two comparison maps corresponding to the identity yield the unique natural isomorphism. I checked that its first-component map is the canonical restriction identification; this matters for the specific section formula in step 8.

Step 6 uses the cochain-complex, cohomology/acyclicity, and homotopy definitions exactly as stated in their three cited nodes. Applying an additive exact equivalence to the differential and the equations proves the component claims, including reflection of acyclicity. There is no bounded-below assumption, totalization, or convergence assertion. Step 7 invokes only the definition of K-injectivity: a map from an acyclic first component has a null homotopy, and (h,0) is a null homotopy in the product. The equation and its transfer are explicit, so there is no hidden general preservation lemma to create.

Step 8 uses the evaluation and coefficient-map construction in def-weil-proetale-module-direct-image. The equality qs=1 identifies the first component over each W with W itself; the other component contributes zero. I wrote the coefficient-map identity using the uniqueness of its extension from constant presheaf sections, not by assuming that arbitrary sheaf sections are globally constant. Naturality for a site arrow is equality of restriction maps; naturality for a module morphism is equality of its component maps. Applying that equality to differentials, chain maps and degree-minus-one homotopies proves all requested compatibilities, rather than asserting transport without an argument.

All cited node statements were opened and copied verbatim into citations.json. The generic off-unit geometric, localization, exact-pullback, and adjunction tools are declared in split_report.tool_uses. No statement dependency or proof dependency is a new definition, restatement, source-only citation, or etale result applied to a pro-etale object. All proof steps are below 2000 characters. I checked empty X (then all module sheaves on X are zero), empty Z (s is an isomorphism), zero coefficient ring, q=1 and s=1, and complexes unbounded in both directions. The product, zero insertion, and null-homotopy computations still work. No properness, separatedness, Noetherianity or invertibility hypothesis was inserted.

Mathlib search hits were read: CochainComplex.IsKInjective and its bounded-below injective theorem define or partially support the homological notion; HomologicalComplex.extend extends complex shapes, not site components. Scheme.coprodPresheafObjIso in AlgebraicGeometry/Limits.lean:480 concerns the structure sheaf on opens of a scheme coproduct, not the category in this item. The targeted grep of AlgebraicGeometry/Sites returned no component-category theorem. The second semantic phrasing reached these scheme coproduct hits and still did not state the item. Every added search record corresponds exactly to an executed msearch query; historical records on the imported item are retained.

## Unfinished work

No mathematical obligation in this one-level split remains. The existing cited nodes retain their own statuses. Maintainer independent review follows delivery.
