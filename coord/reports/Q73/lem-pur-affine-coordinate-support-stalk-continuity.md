## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-affine-coordinate-support-stalk-continuity.json`: item, statement; split in nine steps using nineteen existing nodes. Mathlib searches do not match the full assertion.
- `citations.json`: verbatim statement quotations for every cited node at every proof step.
- No new nodes; no Mathlib leaves; no unit record changed. `searches.jsonl` preserves the actual search results.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint id and by coordinate/support/stalk/continuity concepts. The affine-coordinate hits concern coherent module stalk comparisons, not local etale cohomology with its open-complement exchanges. No project declaration states all clauses of the item.

## WANTED

None. The sources used are present locally.

## Findings and corrections

The statement is retained. Its finite etale twists are explicitly realized as the pullbacks of the finite coefficient lines over the algebraically closed ground field; there is no assertion of continuity for an infinite twist or integral inverse limit. Added the existing finite-etale twist definition to statement dependencies to make this interpretation explicit.

The source citation 09XP is a section, not the tag of a kernel/cokernel theorem. Read the actual theorem in that section, Tag 0A45 (`lemma-cohomology-with-support-triangle`), and use its degree-zero/one exact sequence and shifted higher-image calculation. The module version is supplied by the existing `lem-pur-etale-injective-support-sequence`, whose source is Tag 093X. Tag 0EYM is used for the punctured-open higher images only; it does not itself assert supported continuity.

A potential coefficient gap is avoided using `lem-weil-pbc-exchange-forget-coefficients`: the abelian theorem becomes the actual module comparison, with all transition/limit squares cartesian. Forgetting scalars is never assumed to preserve injectives. A potential map gap is avoided by writing the kernel comparison on resolutions and its homotopy independence, rather than choosing an arbitrary triangle completion. Affine intersections are not assumed affine. No purity theorem, finite-stage coordinate orientation, SGA source or ancestor theorem is used to prove this auxiliary continuity lemma.

## Searches and duplicate checks

Read the inherited item's recorded searches and retained them. Ran fresh logged leanfinder, loogle, grep and leansearch searches under Q73, including a second semantic phrasing. Inspected the returned signatures: Zariski structure-sheaf stalk formulas, localizations, and general sheaf colimit constructions do not give supported etale continuity. The grep hit in Mathlib/AlgebraicGeometry/Limits.lean concerns the stalk map of a scheme limit and does not give the item.

Searched the entire DAG by 0EYM, 09XP, support localization, stalk exactness, exact filtered colimits, and coefficient forgetting; read the statements of all nineteen dependencies. Ran blueprint_refs searches for support continuity, supported geometric stalk, affine continuity, coordinate, and 0EYM, and the ancestor query. Existing nodes give the individual tools but no blueprint node states the whole item. No new nodes were needed: the passage from the exact sequence to its kernels and cokernels is carried in the item's steps.

## Not duplicates

No new nodes were created. The item is not `lem-kun-0eym`: that node concerns higher direct images of abelian sheaves, whereas this item derives supported module stalk continuity and the specified coefficient, Kummer and refinement compatibilities. It is not the ancestor coordinate-model or finite-stage orientation theorem: neither one is used here.

## Review by Q73

I read the fixed smooth-purity chapter and the affine-line/Kummer unit. This auxiliary item retains the route of the coordinate-model extraction through affine limits; it does not replace it by smooth purity or arbitrary-base purity. I read the current main-20261015 frame-independence proof and the current coordinate-model node to locate the ancestor clause and its actual use of this item. I read Stacks etale-cohomology.tex at 0EYM, 09XP/0A45 and 03Q1, and sites-cohomology.tex at 093X and the construction of the flat-pullback base-change map. The proof_origin is agent: the sources supply the two basic inputs, while their combination and the refinement checks are written here.

For step 1 I checked the affine-space and open-immersion definitions. The finite principal-open cover gives qcqs of the open immersion even when R is non-Noetherian; pulling back each principal open gives affine transitions. The universal-property argument shows the punctured scheme is the inverse limit, rather than inferring this from an unsupported pointwise assertion. The zero-ring case has no point.

For step 2 I checked the finite-etale twist definition, tensor/dual definition of integer twists, and specifically the finite reduction clause of the twist-local-freeness node. Since k is algebraically closed and N is invertible, the distinct roots give a constant finite roots sheaf. The negative twists are dual finite lines. Only the finite reduction is used from the pro-etale twist node. No inverse image is claimed to commute with an integral inverse limit.

For steps 3 and 4 I checked that the injective-support node explicitly states a short exact sequence of module complexes, identifies the support complex and the open derived image, and includes the connecting arrow. The resolution-existence node supplies degreewise injective K-injectives on small representatives of the sites. The bounded-below derived-injective node computes the nonnegative resolution, giving negative vanishing. The exact module inverse-image node applies to arbitrary scheme maps with constant A, and the K-injective comparison principle supplies the lift and its homotopy uniqueness. Applying the ordinary open exchange before taking the kernel gives exactly the supported morphism of the item. Kernel inclusions and the unit square determine it on complexes; the argument does not infer uniqueness of a map between distinguished triangles from their middle and right objects alone.

For step 5 I checked the complete 0EYM statement: nonempty small directed poset, affine transitions on both sides, qcqs components, arbitrary sheaves, canonical degreewise exchanges. Step 1 checks these geometric assumptions. The coefficient-forgetting node states both the derived-direct-image isomorphism and its compatibility with the exchange for a cartesian square; the coordinate squares satisfy that additional hypothesis. The stalk/colimit node commutes with arbitrary sheaf colimits, and the upperstar-stalk node gives the stalk at the composed point. These give precisely the displayed colimit of higher-image stalks. All maps have their A-action from the module constructions, so the resulting bijection is A-linear.

For step 6 I checked that the stalk-exactness node really states exactness on abelian etale sheaves and the filtered-colimit-exactness node really applies to systems of long exact sequences. Underlying exactness detects module exactness, so the degree-zero kernel and degree-one cokernel argument is legitimate for A-modules as well. The higher-degree identification uses q=d-1 with q at least one. This explicitly handles degrees zero and one, which cannot be replaced by the shifted higher-image formula.

For step 7 I checked the supported-cup node: it applies to arbitrary k-scheme morphisms and arbitrary n, not just finite-type schemes, and its statement includes Kummer pullback, individual boundaries, and ordered supported products on small etale sites. The support-kernel definition supplies the global-to-stalk factorization, so the compatibility is with actual germs. The basis calculation verifies only the coefficient-line tensor/dual identifications asserted by the item; it does not assert a multiplicative isomorphism for arbitrary pairs of local cohomology complexes.

For step 8 the elementwise module-colimit node supplies representatives and eventual equality, proving cofinal invariance without invoking an unstated cofinality theorem. For localization, each fraction and each equality is already at a stage containing f. In particular R_i[1/f] embeds in R[1/f]: if a/f^m becomes zero, some f^N a=0 holds in R and hence already in the subring R_i. Thus these really form a directed family with union R[1/f], even if f is a zero divisor. The localization squares are cartesian. At overlapping affine neighbourhoods I used affine/principal neighbourhoods around the point inside the intersection, rather than assuming their full intersection is affine. Agreement requires exactly the finite-stage orientation compatibility stated in the item.

For step 9 I computed the full-support kernel directly and checked the empty coordinate product. I also tested b=1, d=0 and d=1 (the kernel/cokernel cases), negative d, r negative, ramified E with arbitrary n, the zero ring, nilpotent localization, a finite-type R with a terminal algebra stage, and cofinal families missing the initial stage. None require a regular or Noetherian limiting base. Every non-elementary step has explicit cited statements; none exceed 2000 characters. B1--B10, C1--C8, D1--D5 and E1--E7 were checked against the files: no new clause-as-lemma nodes, no uncited purity input, no coefficient category switch, no hidden affine-intersection assumption, and no SGA route.

## Unfinished work

None in this stage-1 split. The nineteen cited existing statements remain separate DAG obligations in their own right.
