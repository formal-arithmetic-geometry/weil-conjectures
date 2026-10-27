# Q09 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-principal-relative-pseudocoherence-gluing.json`: statement unchanged; eight-step split of Stacks Tag 09VE (1) implies (2); not a Mathlib leaf.
- `citations.json`: verbatim statements for every step/node citation.
- `searches.jsonl`: actual command-produced search log. No new nodes and no new Mathlib leaves.

## Attachments

None. Searched the project under `lean/WeilConjectures/` for the exact item tag and for principal/relative/gluing pseudo-coherence. The principal-model declarations concern absolute affine finite-free models; they do not state the polynomial-space pushforward assertion for arbitrary E. There is no attachment claiming a sorry-containing declaration is finished.

## WANTED

None. All sources used are in the read-only repository.

## What was wrong and what changed

The item was statement-only and its statement is correct. I supplied the finite unit-relation hypersurface argument of 09VE, filling its missing local chart comparison as described below. I did not change its statement or dependencies needed to state it. All substantive ingredients already have nodes, so creating new nodes would duplicate existing work. The two explicit one-equation finite free resolutions are elementary steps, not new nodes.

The nearest-ancestor command prints None. I retained the inherited null ancestor and its via chain, whose place explicitly identifies the direct-images proof (3), the Knudsen cohomology support, 09UJ and 09VE. I read `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, as well as the DAG chapter and unit records. The blueprint searches `pseudo-coherent`, `closed push pseudo`, `polynomial embedding`, `09VE`, `pseudo`, and `09VA` found no alternate blueprint statement of this item. The generic filtered pseudo-colimit match for `pseudo` is unrelated. No unit or chapter route was changed.

## Source error

Tag 09VE, `more-morphisms.tex`, `lemma-glue-relative-pseudo-coherent`, ends by asserting that the ring of W_i is a polynomial ring over R. This is false literally. For one covering index, no x variables, and R=k a field, its ring is k[y,z,1/y]/(yz-1)=k[y,y^{-1}]. It has the nonconstant unit y and is not a polynomial k-algebra (the units of a polynomial algebra over k are constants). The item itself needs no correction.

The correct elimination is B[1/y_i] = C_i[1/y_i], where C_i retains every variable except z_i. I use the explicit elimination statement already in `lem-weil-pbc-linear-equation-localization-polynomial`, then embed this Laurent chart into the polynomial scheme Spec(C_i[v]) by y_i v-1. This hypersurface has a two-term finite free structure-module resolution. The polynomial-embedding invariance lemma, followed by the reverse implication of the closed-pushforward comparison, establishes pseudo-coherence on W_i. Thus the source's auxiliary-hypersurface route is preserved and its gap is repaired without presupposing the desired gluing theorem.

## Mathlib searches

All new searches were run through the required msearch.py command, and I read its actual hits. The inherited four search records were retained. LeanFinder was tried with both the original relative m-pseudo-coherence phrasing and a second formulation about derived pushforwards along a basic open covering. The first returned affine-cover and HasRingHomProperty facts; the second returned AffineTargetMorphismProperty.IsLocal.of_basicOpenCover, of_affine_open_cover, and related morphism-locality facts. These do not provide the locality hypotheses for this property of a derived complex and do not state the item. LeanSearch returned ordinary gluing of morphisms and glued spaces. Loogle for `"pseudo_coherent"` returned no hits. Grep for `pseudo.*coher|coher.*pseudo` in AlgebraicGeometry and for `PseudoCoherent|pseudo_coherent|pseudoCoherent` in all Mathlib returned no hits. No service failure was represented as an absence result.

## Not duplicates

No new nodes. Existing nodes were found and reused for polynomial-embedding invariance (09VC), the absolute closed-pushforward comparison (09VA), the affine unit-ideal cover criterion, affine finite-type algebras, polynomial elimination, associated-sheaf finite limits and colimits, ordinary affine pushforward, derived composition, open restriction, and composition of derived pullbacks. In particular, I do not cite the broader relative all-affine-charts, flat-ambient or closed-support comparison nodes: their proofs depend on this item and would create a cycle.

## Review by Q09

I read the item's source in `more-morphisms.tex`, Tag 09VE, together with its preceding Tag 09VC (`lemma-relatively-pseudo-coherent`) and the restriction context. I read Tag 09VA in `perfect.tex` (`lemma-closed-push-pseudo-coherent`), whose statement covers arbitrary unbounded derived objects when the pushed structure module is pseudo-coherent. I also read `schemes.tex` Tag 01HV (`lemma-spec-sheaves`, including the final exactness paragraph), 01I7/01ID (associated sheaves and colimits), and 01I9 (`lemma-widetilde-pullback`, ordinary affine pushforward). For the local algebra I read `smoothing.tex` Tag 07EU (`lemma-final-solve`) and its existing DAG node, which states the full elimination formula omitted there. I checked Tag 00E0's basic-open/unit-ideal criterion, Tag 01T2's affine finite-type criterion, and `cohomology.tex` Tags 08FE, 0D5T and 0D5S for the three derived comparisons. There are no new nodes with additional sources to audit.

I opened the statement of every cited node and checked the use against that statement, rather than its proof. The checks for the eight steps are:

1. `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` explicitly applies to an arbitrary indexed family, so membership of 1 in the generated ideal gives a finite sum, not an unjustified finite-index assumption. `lem-weil-pbc-lft-affine-pairs` applies to the given finite-type affine morphism over the whole affine base. Its finitely many algebra generators give a surjection without requiring finite presentation. `def-weil-closed-immersion` includes the affine quotient characterization, and `def-nagata-relative-affine-space` identifies the finite polynomial spectrum with relative affine space. These give the two actual closed embeddings of step 1.
2. The y-degree recurrence proves injectivity over an arbitrary coefficient ring. `lem-sc-tilde-preserves-finite-limits` supplies only the kernel part; I separately cite `lem-weil-pbc-affine-tilde-gamma-adjunction` for preservation of cokernels. Thus I do not take full exactness from a finite-limit statement. `lem-weil-pbc-pushforward-tilde-spec` identifies the quotient sheaf with the actual q-pushforward of O_T. A bounded finite free resolution is the bounded-above finite free model allowed by `def-pur-pseudo-coherent-complex`.
3. I corrected a potential C4 error during self-review: `lem-weil-pbc-spec-localization-away-basic-open` states a topological homeomorphism only. The delivered proof instead cites clause (0) of `lem-weil-pbc-affine-ideals-closed-subscheme`, which explicitly says that a principal open is affine and its coordinate restriction is a localization. The existing polynomial-elimination node applies with coefficient ring R[x,y], r at least 1 and coefficients y_j; the chosen i ensures r at least 1. It gives the stated formula for z_i and preserves every retained coordinate. The inverse-coordinate quotient is justified by the two written inverse maps, and its surjection is exactly what the closed-immersion definition requires.
4. The recurrence in the inverse coordinate v proves injectivity of y_i v-1 without requiring y_i to be regular in R. The same three associated-sheaf statements as in step 2 give the second structure-module resolution. This explicitly verifies the key hypothesis for reflection by 09VA; finite presentation alone would not suffice.
5. Both local closed embeddings are checked by surjective algebra maps. The x_j generate A, and adjoining the image of v supplies b_i^{-1}, so there is no hidden extension argument for the composite. Finite type of U_i over S follows from these finite generators; the cited affine-pair and quasi-compactness statements also verify the geometric hypotheses of 09VC. The local ambient polynomial ring has finitely many variables.
6. `lem-sfb-affine-polynomial-embedding-pseudocoherence-invariance` states exactly the comparison of the given embedding with j_i, for the same integer m and arbitrary E. `lem-pc-derived-direct-image-composition` applies to these scheme morphisms and arbitrary derived objects. `def-sfb-m-pseudo-coherent-complex` makes isomorphism invariance elementary by composition of approximation maps. `lem-sfb-closed-pushforward-pseudocoherence` has both directions and no quasi-coherence hypothesis, so its reverse implication applies after step 4 to the object R(k_i)_*(E restricted to U_i).
7. `lem-pc-restrict-derived-direct-image-open` uses precisely an inverse-image open; k^{-1}(W_i)=U_i follows from y_i mapping to b_i. The unit relation proves that W_i cover T. The definition of absolute m-pseudo-coherence then gives a single refined open cover of T; no descent theorem for global finite-free approximations is assumed. The nested restriction targets are identified by `lem-pc-ringed-spaces-derived-pullback-composition`, whose statement includes the unbounded scheme case. The empty-cover case is explicitly treated.
8. The forward direction of the same absolute closed-pushforward node applies to q because step 2 proved the required structure-module hypothesis. The composition comparison identifies the resulting object with the requested polynomial pushforward. The original map P to A remains surjective, so the final map is a closed immersion as claimed.

I tested the construction for X empty, S empty (hence X empty), an empty principal covering, a one-element covering with b a unit, and coefficient rings with nilpotents and zero divisors. For the empty sum h=-1 the multiplication map is still injective and B=0; for r=1 the Laurent chart explains precisely the source error. No degree bound or finite presentation of A was assumed; all integers m, arbitrarily large index sets and non-quasi-coherent E remain allowed.

Against delivery-errors B: no new statement-only nodes are needed, the statement's objects and existing definition citations remain intact, and the source tags and actual recorded searches are retained. Against C: each non-elementary input has a cited node and every citation has its verbatim statement in citations.json; no parent relative-pseudo-coherence result is used. Against D: the eight steps construct and compare the auxiliary hypersurface instead of moving the item into a renamed lemma. Against E: the source's false polynomial-ring assertion is repaired, both structure-module hypotheses are proved, and the inverse maps and recurrences are written explicitly. Every step is under 2000 characters; no long step hides a lemma. Off-unit citations are declared as generic tool uses in split_report, without changing top-level tool_uses.

## What could not be finished

Nothing mathematical remains open in this one-level split. The independently unsplit existing prerequisites stay with their current owners. Required server dry run and push are the delivery operations for this report.
