# Stage-1 report: lem-sfb-space-perfect-tensor-test-holim

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-tensor-test-holim.json: statement, now split; no Mathlib match.
- citations.json: twelve entries, one for each step/node citation, checked as literal substrings of the cited statements.
- searches.jsonl: five actual searches recorded by msearch.py for this item, with two semantic phrasings; results read.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The item statement and statement dependencies are unchanged.

## Attachments

None. Searched the live WeilConjectures source by the exact blueprint tag and item id and by perfect/tensor/product/holim concepts. No declaration states the item. Existing sorry-bearing project statements are not counted as attachments.

## WANTED

None. The Stacks sources used are available locally.

## What was wrong or missing

The item was an unsplit supporting lemma. The DAG already contains the strictly more general lem-sfb-space-perfect-tensor-global-limits: it quantifies over arbitrary families and arbitrary towers in the ordinary derived subcategory, rather than only the item's countable families and strict towers. Creating a new product-preservation or Roos-comparison node would duplicate it. I therefore reuse that existing statement, as required by the duplicate rule, and explicitly discharge its hypotheses and the separate product-existence clause. This is not the creation of a node restating the item.

The existing blueprint ancestor command returns `blueprint.from.node = None`. I retain that live null ancestor and its explicit inherited place, rather than invent a blueprint node. I read the current latest chapter and sk-thm-sf-ctf-stability statement and proof; this is a supporting coherent-family-effectivity argument inherited from the older direct-image-preservation paragraph, not a replacement of the unit route. The current unit record and latest blueprint differ historically, but neither is modified. Searches of the whole imported blueprint for perfect products, tensor global, derived Hom, products, homotopy inverse, and coherator found no separate blueprint statement of this item.

The source specifically does not justify replacing a product in D_QCoh by an ambient derived product. Steps 2 and 3 keep these distinct: construct the ambient product by K-injective representatives, then apply the right adjoint of the full inclusion. No assertion that the ambient product is quasi-coherent is made.

## Not duplicates

No new node was created. Existing lem-sfb-space-perfect-tensor-global-limits is reused as a stronger statement of the tensor-test assertion. The item is not marked merged because this delivery changes only its authorized split; this overlap is reported for the maintainer.

## Review by Q129

I read spaces-flat.tex, Tag 0CX6, lemma-compute-against-perfect, including the paragraph asserting exact global derived Hom preserves products and derived limits and its final conversion from Hom to tensor tests. I also read sites-cohomology.tex, Tag 08JJ, lemma-dual-perfect-complex, including its local strictly perfect dual calculation; spaces-perfect.tex, Tag 0CR4, lemma-better-coherator, at the derived full-subcategory inclusion; and injectives.tex, Tag 07D9, lemma-derived-products, including the K-injective product construction. I checked every cited node's statement, rather than taking assertions from its proof. No new nodes need independent source attribution.

Step 1 uses the affine-etale-atlas node to obtain an atlas from point-space quasi-compactness, and the affine-chart-pair characterization to turn the absolute diagonal condition into the coherator's stated hypothesis. The affine-scheme-qcqs node supplies quasi-separatedness of Spec A; the space-qcqs-permanence node then says exactly that f is qcqs. The perfect-uniform-tor node explicitly supplies the needed quasi-coherent cohomology of E; I do not infer it from the definition node alone. None of these nodes requires X Noetherian or f proper. The atlas and chart-pair statements are applied over Spec Z, so absolute rather than relative quasi-separatedness is used.

Step 2 uses the small-ringed-model definition for the existing equivalent small site. The K-injective-resolution theorem applies because that site is small and its structure sheaf is commutative. The K-injective Hom-computation node applies to any abelian category and any complex N; it has no boundedness restriction in its unbounded clause. I wrote the product argument explicitly: maps into the termwise product are coordinate maps, a null-homotopy is a coordinate family, and coordinate null-homotopies combine to show that the product is K-injective. The derived Hom universal property then follows from the cited bijection. This is a short elementary calculation from those statements, not an unrecorded sheaf-product-exactness theorem. In particular, products of module sheaves need not be exact.

Step 3 uses the actual Hom bijection in the derived-coherator-adjunction statement. Its hypotheses were checked in Step 1. Applying that bijection to the ambient product gives the displayed four-term Hom calculation. Fullness identifies the last Hom sets, so the counit/projection maps give the product in D_QCoh. This proves existence in the source category rather than merely assuming it from notation in the general tensor-test node.

Step 4 uses the statement of the existing space-perfect-tensor-global-limits node. It states exactness and arbitrary product preservation for precisely the small-etale quasi-coherent derived category, with the base-induced A-action. Step 1 supplies its qcqs-morphism and perfect-in-C_X hypotheses, and Step 3 supplies the products. Its comparison is explicitly the one induced by projections, so it gives the exact map of the item. I did not replace A-modules by abelian groups or condensed modules.

Step 5 uses that same node's product-triangle clause, which explicitly identifies the image transition and the distinguished triangle. I checked the transition equality after every product projection and wrote it out. The derived-limit definition states a property of an object with a Roos triangle, with no functorial cone chosen. Thus we may use the displayed image triangle as the target derived-limit representative, obtaining the required arrow compatibility without claiming a unique or canonical filler. This matches the item's wording that an isomorphism can be chosen.

I tested X empty and A the zero ring (the derived categories and displayed products are zero); E zero (the test functor and its triangles are zero); X affine with E equal to O_X (ordinary derived-module products and Roos triangles); and arbitrary unbounded families and nonsurjective towers (the argument uses K-injectives and categorical products, never termwise exactness of sheaf products or a Mittag-Leffler hypothesis). These cases cause no change in hypotheses. I found no statement dispute and changed no statement.

The searches returned affine scheme limit facts, ordinary flat tensor preservation of finite limits, light condensed monoidal facts, and homotopy-category implementation files. These are not the item: no hit gives quasi-coherent unbounded derived global sections with a perfect tensor factor. The second semantic phrasing gave the same mismatch. All five query texts in the appended mathlib_searches entries come verbatim from the local msearch log; no unavailable service was relabelled absent.

I checked B through E of delivery-errors: no unsupported new statement or duplicate node; all definition and theorem citations have their actual meanings; all twelve citation quotes are literal; source products are internal; the affine and coherator hypotheses are discharged; the product transition is checked component by component; and no new dependency is circular. Every step is shorter than 2000 characters. The three off-unit generic tools are declared in split_report.tool_uses: affine-scheme qcqs, K-injective existence, and Hom into K-injectives. They discharge categorical hypotheses, rather than replace a unit proof step. No SGA source is used.

## What could not be finished

Nothing mathematical remains in this one-level split. The existing stronger lemma remains its own unsplit item; this delivery does not modify or split it.

## Validation

Required deliver.py --no-push exited 0 and printed OK at e82dda26aca: server preflight passed, including the DAG and split checks. The first dry run requested a longer quote for perfect-uniform-tor; it was replaced by the entire relevant sentence, and the successful rerun checked it. No mathematical changes were required.
