# Stage-1 delivery: lem-sfb-proper-curve-automorphism-scheme

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-curve-automorphism-scheme.json: item, statement, split into seven steps; no Mathlib match.
- citations.json: a verbatim statement quotation for every citation in every proof step.
- report.md: this report and signed review.

No new nodes, no new Mathlib leaves, no unit record edits, and no Lean edits. Search outputs and the msearch log remain in the sandbox.

## Attachments

None. Searches of lean/WeilConjectures/ by the exact blueprint tag, by proper-curve automorphism terminology, Isom representability and schematic-locus terminology found no declaration giving this whole item. Existing scheme-group, Galois automorphism and curve-cohomology declarations do not give its representing functor on all test schemes. The earlier item had no finished Lean attachment.

## WANTED

None. All sources needed for this split are available in literature/.

## What changed and what was wrong

The imported item had a correct statement but no proof. Its statement, statement dependencies, source, created record and inherited blueprint ancestry have been preserved. I added a proof, its dependency union, an agent proof-origin record, the split report and actual Q32 Mathlib searches. I retained the pre-existing searches rather than rewriting their results.

The source's usual argument is to pull back the separated finite-presentation diagonal of the stack of curves and then apply Tag 0B8F to the group algebraic space. Here existing projective Isom-graph representability gives a scheme directly: first use the already existing lemma on separated dimension-at-most-one spaces, then the proper-curve projectivity theorem. Thus 0B8F remains a source pointer but is not used as an uncited theorem. This stays below the unit route and supplies the same automorphism input for the DM-locus criterion.

I read the chapter, unit, current blueprint unit and direct-images proof. This is a supporting node, not the unit's key statement, so the unit realization fields are not mine to fill. The inherited ancestry has from.node null, as confirmed by blueprint_refs.py ancestor; I preserved it and the exact non-unspecified place and via list. Whole-blueprint searches for automorphism scheme, proper curve, algebraic space scheme, 0ADD and codimension one found no imported blueprint node stating the item. In particular same_as remains empty.

## Not duplicates

No new nodes. I reused lem-sfb-separated-space-dimension-one-scheme, lem-sc-proper-dim-one-projective and lem-sfb-projective-curve-isom-graphs after opening their statements. The first is already present in the current shared DAG (Q36); I did not create a second schematic-locus node. The graph theorem treats pairs of projective flat families, while this item constructs the group operations for one proper algebraic space over a field.

The projectivity and field-extension dimension lemmas are generic tools outside this unit; their reasons are declared in split_report.tool_uses for the maintainer. They only verify prerequisites of this unit's graph theorem and do not replace the unit route.

## What remains

No missing proof step at this level. Existing non-Mathlib prerequisites remain their own DAG tasks. No claim is made that the underlying Lean proofs are complete. No new sorry is introduced because no Lean is written.

## Review by Q32

I read Stacks moduli-curves.tex Tag 0DSQ (lemma-curves-diagonal-separated-fp), including its graph/Hilbert boundedness argument, and the opening of the section on finite reduced automorphism groups. It explicitly treats dimension at most one without smoothness, reducedness or stability. I also read spaces-more-groupoids.tex Tag 0B8F (lemma-group-space-scheme-locally-finite-type-over-k), and checked that its separatedness and local finite-type assumptions would be met by the usual route. Our existing projective graph theorem avoids needing that additional dependency.

For step 1 I read spaces-over-fields.tex Tag 0ADD (lemma-codim-1-point-in-schematic-locus) and the full statement of lem-sfb-separated-space-dimension-one-scheme. That node already states the required global consequence for a separated space locally of finite type over a field. Properness supplies these hypotheses by the inline algebraic-space convention in the item. The node permits empty, disconnected and nonreduced spaces. I removed an initial citation of the scheme-only properness definition from this step: no scheme-only theorem is applied before we have proved that C is a scheme.

For step 2 I read varieties.tex Tag 0A26 (lemma-dim-1-proper-projective) and lem-sc-proper-dim-one-projective. Its statement supplies an actual closed embedding, including the empty scheme, and its only hypotheses are precisely properness and the original dimension bound. Projectivity is a conclusion here, not an added assumption on the item.

For step 3 I read pqf-def-locnoeth and its affine-cover definition. The written argument that every ideal of a field is 0 or the whole field proves the one needed Noetherianity fact explicitly. This is the only elementary standalone step.

For step 4 I read every cited statement: lem-pc-flat-field gives flatness of every scheme over K; pqf-lem-lft-fp-locnoeth requires a locally Noetherian target and a locally finite-type map and gives local finite presentation; lem-pc-separated-quasi-separated turns the already available separatedness into quasi-separatedness. The definition def-sbc-locally-finite-presentation explicitly says finite presentation is local finite presentation plus quasi-compactness and quasi-separatedness. I checked morphisms.tex Tag 01TX (lemma-noetherian-finite-type-finite-presentation) and schemes.tex Tag 01KK and its following paragraph as well. Properness supplies quasi-compactness and local finite type. No finite-presentation assertion is borrowed from the definition alone.

For step 5 I read the field-extension clause of lem-kun-dimension-extension and its definition def-kun-dimension, which is topological Krull dimension. I checked algebra.tex Tag 00P3 (lemma-dimension-preserved-field-extension), including its finite-type hypothesis. This applies to C because it is now a scheme finite type over K. The clause is for every field extension; hence it applies to all algebraically closed geometric fibres and preserves the bound at most one, including the empty case. I use no dense-open clause of that node.

For step 6 I read the entire statement of lem-sfb-projective-curve-isom-graphs. It explicitly gives a scheme, separated and of finite presentation, and a graph bijection natural under arbitrary base change. The base is the locally Noetherian scheme Spec K, the two families are both C, and steps 2, 4 and 5 verify all projectivity, flatness, finite-presentation and geometric-dimension hypotheses. No Noetherian assumption on T is present in that theorem. Finite presentation implies finite type here by the explicitly written finite-generation argument and the retained quasi-compactness; this uses the meanings in the two cited definitions rather than an unstated permanence theorem.

For step 7 I read categories.tex Tag 001P (lemma-yoneda), the full statement of lem-galois-yoneda-fully-faithful, def-pc-fibre-product and def-sc-group-scheme. The cited Yoneda node is exactly the bijection from natural maps between representables to morphisms, with faithfulness, which is what the step uses. I do not use the more general evaluation form of Yoneda without citing it: the displayed universal-point formulas use the already supplied representing bijections theta. The fibre-product definition supplies the identification of pairs of points. Composition and inversion commute with pullback by the written functorial equations; Yoneda then gives genuine scheme morphisms. The associativity, unit and inverse diagrams are checked on every test scheme, so faithfulness applies. The final formula theta_(T')(g composed with v) = v^*theta_T(g) is exactly naturality of the graph bijection, and therefore also applies to nonreduced T and T'.

I checked small cases: C empty gives the singleton automorphism functor represented by Spec K; C=Spec K does likewise. Zero-dimensional nonreduced C is included by the same graph theorem, with no reduction step. P1 gives the positive-dimensional automorphism group, so no unjustified finiteness or etaleness conclusion is asserted. Proper elliptic curves and disconnected curves are not excluded. The known possibility of nonreduced automorphism group schemes in positive characteristic is compatible with every step: no argument tests only geometric points or replaces a functor by its reduction.

Against delivery-errors B through E: there are no new nodes to be hidden clauses, duplicates or unsearched lemmas; all objects in the item were already introduced, and the statement is unchanged. Each non-elementary invocation has a cited statement with the exact hypothesis and conclusion used. citations.json copies actual statement text for all sixteen citations. The proof dependency list equals their union. All seven steps are below 2000 characters; the group-structure step is one ordinary application of representability and Yoneda with its formulas written out, not a hidden comparison theorem. Mathlib searches were run through msearch.py in two semantic phrasings plus LeanSearch, Loogle and grep. Their Galois-category, elliptic-coordinate and general Yoneda hits do not assert this representability theorem. The server review_split check passed before the final report; the full dry run follows.
