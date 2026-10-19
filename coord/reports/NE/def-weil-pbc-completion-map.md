# Stage-1 repair: def-weil-pbc-completion-map

## Files written

- dag/nodes/sec-proper-base-change/def-weil-pbc-completion-map.json: definition, split; explicit strict-complex completion morphism, not a Mathlib leaf.
- citations.json: empty because a definition has no numbered proof steps.
- report.md: this repair report replaces the earlier incorrect certification.

## New nodes

None. All seven construction inputs already exist in the DAG. No Mathlib leaves were created.

## Attachments

None. Searching both read-only project Lean trees for the blueprint tag, comp_K and completion-map wording gave no exact finished declaration of this definition. The upstream master remains reference material, not a finished-proof attachment.

## WANTED

None.

## Statement corrected

STATEMENT-DISPUTED: with the current dependency, the imported phrase “the map induced by the compatible quotient arrows” is underdetermined. The dependency explicitly permits any chosen distinguished Roos triangle and specifies no induced morphisms. Stacks derived.tex Tag 08TC (definition-derived-limit) and Tag 0H9J (remark-functoriality-derived-limit) distinguish that property from a functorial selection of cones and warn that a morphism completed by TR3 is not unique. Compatible arrows in the derived category alone supply no selected lift or selected nullhomotopy.

The correction faithfully implements the source's intended additional data: the detailed proper_base_change.tex definition at lines 5035--5051 is a complex cone model, not a claim that triangulated cones are functorial on arbitrary arrows in the derived category. Fix one K-flat representative F of K, use its tensor reductions at every level, and form the termwise product B and C = Cone(1-s)[-1]. The quotient maps are strict chain maps a_n with t a_{n+1}=a_n. The selected map is j(x)=(0,a(x)), localized and precomposed with the representative isomorphism's inverse. This construction fixes the object and the map simultaneously. It does not select an arbitrary lift into an unrelated chosen triangle. The old inverse-limit node is retained only to identify the derived-limit property of this explicit cone.

No coefficient hypothesis was changed: Lambda is commutative Noetherian, I is finitely generated, Lambda/I is additively torsion, and all Lambda/I^n are perfect. K remains arbitrary and unbounded. A K-flat representative is construction data whose existence is supplied by the cited resolution theorem, not an extra hypothesis on K. No condensed coefficient category is identified with this category of constant-ring module sheaves.

## Review by NE

I read the complete maintainer review at /home/ubuntu/weil-launcher-nt/reviews/NE__def-weil-pbc-completion-map__25149030cc0b/review.md. Both findings are repaired: C4/E4 by specifying the strict tower, explicit cone, and actual chain map; the report/source-pointer inconsistency by writing the exact detailed TeX document and labels into the JSON source field and removing the earlier false certification. The dependency is an already reviewed node owned by another item, so it was not edited.

For the item I read the detailed TeX definitions of the coefficient datum (lines 5022--5033), inverse limit (5035--5051), and completion map (5131--5139), as well as the master blueprint entry and the chapter/unit route. The source's compatible quotient arrows are realized by x -> x tensor 1 on the same F at all levels. This remains a definition supporting the later Koszul/quotient route; none of the unit's three proper-base-change proof steps is replaced.

I opened and read each of the seven cited statements. def-weil-pbc-complete-coefficient-datum supplies the exact coefficient hypotheses and reduction tower. def-weil-derived-tensor explicitly computes derived tensor by a K-flat representative, including restriction to Lambda coefficients. lem-pc-kflat-resolution provides such a representative for every complex on a ringed site, including unbounded complexes; its source sites-cohomology.tex Tag 06YS, label lemma-K-flat-resolution, was read. def-weil-abstract-derived-category gives localization, shifts and the mapping-cone differential. lem-weil-proetale-countable-products-exact says that products of modules over any commutative ring sheaf on the small pro-etale site exist sectionwise and are exact; it applies to Lambda_X, without qcqs or boundedness assumptions. lem-weil-derived-limit-products-core gives precisely the derived product of arbitrary representative complexes when countable products are exact; I checked derived.tex Tag 07KC, label lemma-products. Finally, def-weil-pbc-adic-derived-inverse-limit gives the distinguished-triangle property and reduction types, but expressly does not give induced maps; the repaired definition no longer takes a map from it. There are no new-node source obligations or numbered proof-step citations.

The small chain calculation was checked explicitly against the cited cone convention. In degree j, C is B^(j-1) plus B^j and its differential is (-d y -(1-s)x,d x). Thus d j(x)=(0,a d x)=j(d x), since the n-th coordinate of (1-s)a is a_n-t_{n+1,n}a_{n+1}=0. Projection onto B's second coordinate recovers a and hence every quotient arrow. For a strict tower map v the product map h satisfies h s=s' h by the transition equation; the induced cone map is (y,x) -> (h y,h x). For a chain map between chosen K-flat representatives the quotient square commutes strictly, and this cone map takes the displayed completion map to the displayed completion map. These are direct coordinate calculations from the definitions, not unstated existence lemmas or claims of functorial cones on an unenriched triangulated category.

I checked zero K, I=0, I=Lambda, the zero ring, and unbounded representatives. Zero reductions give zero C and zero j. When I=0 the strict tower is constant with identity transitions, s is the sequence shift (not zero), and j is the diagonal chain map into its cone; it is explicitly selected even in this case. When I=Lambda the reductions vanish and the construction is still meaningful. The common Lambda_X category is essential: the varying quotient coefficients are restricted before taking products. There is no requirement that the transitions split or are surjective to form this cone.

I checked delivery-errors B--E against the repaired node. No elementary fact or clause has been moved to a new node (D1/D2); no new node or duplicate was created. Searches of the entire DAG and tools/blueprint_refs.py for completion map, functorial cone, strict tower homotopy limit and K-flat resolution identified the existing inputs, rather than replacements. In particular, the existing ringed strict-tower homotopy-limit theorem was read, but its derived-functor construction is not needed for this explicit cone definition. The exact-products and K-flat tools are declared in split_report.tool_uses where appropriate. The imported blueprint.is/from fields and import_flags were preserved.

The Mathlib searches were repeated through msearch.py for the repaired formulation, with a second phrasing. LeanFinder returned generic mapping-cone declarations, then ordinary AdicCompletion APIs. Loogle returned mappingCone and coordinate-map infrastructure; none states this whole derived pro-etale completion-map definition. The targeted grep for mappingCone with limit/completion in Algebra/Homology found no hits. LeanSearch returned Internal Server Error and is recorded as unavailable. The actual queries/results are recorded in the node and sandbox search log; no search was invented.

## What could not be finished

Nothing in the requested one-level split remains unfinished. The definition's only selected data are an existing K-flat resolution and explicit complexes/maps. The second reader should review the repaired construction and deliver; this worker does not push.

## Second reading by NE

- Item statement: checked against `proper_base_change.tex` definition `def:weil-pbc-completion-map` (lines 5131--5139) and its dependency definition (lines 5035--5051); the compatible-arrow wording is repaired by the explicit strict cone model, with the coefficient hypotheses preserved.
- New nodes: none; the item is the sole changed node, so B1--B7 and duplicate-node checks introduce no new statement or search obligation.
- Construction data: checked the seven cited node statements; they supply the coefficient datum, K-flat representative, derived tensor reductions, cone convention, exact products, derived product identification, and only the derived-limit triangle property. No cited statement is used to claim functoriality of an arbitrary chosen triangle.
- Chain calculation: checked the displayed differential and verified `(1-s)a=0`, that `j=(0,a)` is a chain map, and that projection recovers every quotient arrow. The zero complex, `I=0`, `I=\Lambda`, zero ring, and unbounded representatives remain well-defined.
- Blueprint and searches: checked `tools/blueprint_refs.py` for the item and recorded the self ancestor (`node def-weil-pbc-completion-map, order 1258`); the existing Mathlib searches in `searches.jsonl` are actual msearch runs and find no matching derived completion map.

Changes made in this second reading: filled the required `blueprint.from` self-ancestor and exact node place; added this item-by-item audit. No mathematical statement or dependency was otherwise changed.
