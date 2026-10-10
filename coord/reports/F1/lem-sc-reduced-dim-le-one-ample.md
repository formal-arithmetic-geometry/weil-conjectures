# lem-sc-reduced-dim-le-one-ample

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-reduced-dim-le-one-ample.json`: split statement node; no statement change.
- `lem-sc-zero-dim-noetherian-affine`: new unsplit statement, no Mathlib match.
- `lem-sc-integral-dim-one-ample`: new unsplit statement, no Mathlib match.
- `lem-sc-component-intersections-finite`: new unsplit statement, no Mathlib match for the full claim.
- `lem-sc-ample-finite-principal-affine`: new unsplit statement, no Mathlib match.
- `lem-sc-glue-component-line-bundles`: new unsplit statement, no Mathlib match.
- `lem-sc-closed-affine-union-affine`: new unsplit statement, no Mathlib match.
- `lem-sc-conductor-sections`: new unsplit statement, no Mathlib match.
- `lem-sc-ample-ideal-section`: new unsplit statement, no Mathlib match.
- `lem-sc-affine-cap-section-open`: new unsplit statement, no Mathlib match.

## Attachments

None. I searched `WeilConjectures/` for the item tag, ampleness, reduced curves and dimension-one schemes. The ample-existence theorem found there concerns abelian varieties; it does not state this item. No sorry-free declaration states any new node exactly.

## Sources wanted

`WANTED: literature/stacks-project/varieties.tex, Lemma 09NX and its citations 09ND, 09NE, 09NW, for lem-sc-reduced-dim-le-one-ample and four new nodes.` The project's `literature/stacks-project/` is absent in this checkout. I read the corresponding source text in `/home/ubuntu/c1-stacks-review/varieties.tex` and checked the Stacks tag pages.

`WANTED: literature/stacks-project/properties.tex, 0AAX, 0CKV, 09NV, 01Q3 and 01PV, for five new nodes.` I read `/home/ubuntu/c1-stacks-review/properties.tex`.

`WANTED: literature/stacks-project/limits.tex, 09NL, for lem-sc-closed-affine-union-affine.` I read `/home/ubuntu/c1-stacks-review/limits.tex`.

## Source error

The statement of Stacks 09NX is for dimension exactly one, whereas this DAG node says at most one. More subtly, its opening line applies 09ND (which assumes an integral scheme of dimension one) to every irreducible component of a dimension-one reduced scheme. A disjoint union of an integral curve and a closed point is a counterexample to that inference: the point is an irreducible component of dimension zero. The conclusion is still true. Steps 1 and 2 explicitly cover dimension-zero schemes and zero-dimensional components by the affineness result 0CKV. I did not change the item's statement.

## Unfinished

The nine new supporting nodes are deliberately unsplit, as stage 1 requires. LeanSearch returned HTTP 500; LeanFinder and source grep showed no exact Mathlib theorem. No Lean code was written or compiled.

## Review by F1

I read the 09NX proof in `varieties.tex`, not only its statement. Its hypothesis is Noetherian, reduced, separated, dimension one. The item has the same first three hypotheses and a weaker dimension bound; step 1 handles dimension zero (and the empty scheme), after which the 09NX dimension-one proof applies. I read the source labels and statements for every new node: 09ND says exactly the integral dimension-one case; 09NE gives both a line bundle and a glued section under reducedness and discrete component intersections; 09NW gives the conductor restriction identity used in 09NX; 09NV supplies one affine section locus around a finite set; 09NL makes a finite union of affine closed subschemes affine; 01Q3 supplies an ideal-twisted section outside its zero locus; 01PV makes the intersection of an affine open and a section locus affine; 0AAX and 0CKV imply the separated, quasi-compact zero-dimensional branch. The component-intersection node spells out the topological assertion in the first paragraph of 09NX. Searches of the entire DAG by these tags and concepts, and `tools/blueprint_refs.py search` for each concept, found no node with the same statement. The Mathlib source has generic component and affine-open results but no full theorem used as a leaf here.

Step 1 uses only the zero-dimensional affine node, whose hypotheses follow from the item. Step 2 uses the integral ample node on each positive-dimensional reduced component, the zero-dimensional affine node on the isolated components, and the finite-intersection node for $T$; closed subschemes inherit the required Noetherian and separated properties, and their dimensions cannot exceed one. Step 3 uses 09NV with the finite set $T\cap Z_i$ and all of $Z_i$ as the ambient open. Its section is nonzero on each overlap, exactly the extra hypothesis of 09NE, so the gluing node supplies both $\mathcal L$ and $s$. Step 4 uses 09NL only after verifying that each affine $(Z_i)_{s_i}$ is closed in $X_s$ and their underlying sets cover it. Step 5 uses 01Q3 on the quasi-coherent conductor ideal at a point outside its zero set, then the actual definition of ampleness to choose an affine section locus. Step 6 multiplies the two sections, with tensor exponents added, and 01PV applies to the affine locus of the second section. Step 7 uses the conductor node's stated global-section isomorphism and vanishing on the other components, yielding the same affine nonvanishing locus on $X$; the two kinds of loci cover all points, so the cited ample definition gives the conclusion. These are statement uses, not appeals to the proofs hidden inside cited nodes.

I checked the small cases: empty $X$ has affine empty scheme and vacuous ampleness; a single reduced closed point uses the zero-dimensional branch; a disjoint curve plus point forces the corrected component branch; a nodal pair of components has finite $T$ and satisfies the nonvanishing hypothesis of 09NE; $T=\varnothing$ is allowed by 09NV; and for one component the conductor ideal is the unit ideal, so the final construction reduces to the ordinary affine section. I corrected the dimension-one-only route by adding step 1 and by treating zero-dimensional components in step 2. I checked new nodes against B1-B9 (self-contained statements, no proofs, named Stacks tags, no duplicate blueprint), C1-C8 (each non-elementary fact cited, no cycle, no outside-unit tool), D1-D5 (supporting lemmas are smaller than the item), and E1-E7 (hypotheses, objects, edge cases, and the source inference just described). The only unavailable local source is the repository's literature checkout; the mirrored Stacks source was read directly.
