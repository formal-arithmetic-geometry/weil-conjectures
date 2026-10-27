## Worker report

1. Files written: `dag/nodes/sec-curve-estimates/lem-galois-glue.json` (statement, now split; no exact Mathlib leaf for the full relative formulation); `citations.json` (one verbatim statement quote for every step/node citation); this report. No new nodes or new Mathlib leaves.
2. Attachments: none. Searches for the exact blueprint tag and the notions in `lean/WeilConjectures/` found no project declaration giving every clause. The named `Scheme.GlueData` declarations are Mathlib declarations, not project attachments.
3. WANTED: none.
4. The original proof falsely calls both maps from the coproduct of overlaps into the coproduct of charts open immersions. It also leaves the inverse-image identification and compatible uniqueness unjustified. These are repaired below without changing the statement. Statement dependencies now name schemes, open immersions (a Zariski cover means an open cover), and fibre products directly; the conventions aggregator was not a theorem proving gluing.
5. Nothing unfinished in this one-level split. It reuses existing nodes only. No repository writes, Lean writes, compilers, Lake, or local project checks were used.

## Sources and searches

Read the chapter `sec-curve-estimates`, imported unit `sk-prop-h2`, and the current blueprint files `literature/blueprint/latest/blueprint/sec-curve-estimates/sk-thm-curveestimate/lem-galois-glue.md` and its separate proof file. The current blueprint statement agrees with the imported statement; its order and unit location have moved, and its Lean list now points to Mathlib gluing declarations. The old imported source metadata is retained as required. This is the scheme-gluing tool in the blueprint route, not a replacement of the Kummer or curve-estimate argument.

Read Stacks `schemes.tex`, Tag 01JA (`section-glueing-schemes`), Tag 01JB (`lemma-glue`, including the precise open-domain condition and mapping properties), Tag 01JC (`lemma-glue-schemes`), and Tag 01JR (`lemma-open-fibre-product`). Also read `constructions.tex`, Tag 01LH (`lemma-relative-glueing`), to compare its basis-indexed relative formulation. The proof_origin is agent: the existing blueprint argument is corrected and its relative consequences are written explicitly, rather than claiming to follow the distinct basis/functor proof of 01LH verbatim.

Ran whole-DAG statement searches and tag searches for 01JB, 01JC and 01LH. Ran `tools/blueprint_refs.py search` for `gluing`, `glue-schemes`, and `Glueing`, and `ancestor lem-galois-glue`. The results identify the existing general gluing leaf and morphism-gluing leaf, with no second blueprint node stating this relative cover-cocycle theorem. Thus blueprint.same_as is empty. No node was created.

All Mathlib queries are recorded from the actual `msearch.py` log in searches.jsonl. LeanSearch and Lean Finder returned Scheme.GlueData, its glued scheme, and Cover.glueMorphisms; the second phrasing and Loogle returned Cover.RelativeGluingData. Read the source `Mathlib/AlgebraicGeometry/Gluing.lean` (GlueData, glued, open charts, covering, overlap pullback) and `RelativeGluing.lean` (RelativeGluingData, lines 59–129). The latter assumes a category of cover indices, locally directedness, thinness and smallness, whereas the item supplies an arbitrary open cover with pairwise cocycle isomorphisms. Constructing that extra diagram and checking its axioms is not a one-line specialization. The full item remains split; the constituent existing Mathlib leaves are reused. The first grep was restricted to a single file and the wrapper returned the documentation lines; the second grep over AlgebraicGeometry returned file names and declaration lines, including Gluing.lean:202 and RelativeGluing.lean:74. No failed search was recorded as a negative result.

## Source error

In the current blueprint proof, “Both are open immersions” is false. Take Y = Spec(k), the two-member repeated open cover Y_1 = Y_2 = Y, and P_1 = P_2 = Y with identity transition. The overlap coproduct has four copies of Spec(k), the chart coproduct has two, and each source projection maps two copies to the same chart. It is not injective on points and cannot be an open immersion. The individual overlap-to-chart maps are open immersions, which is exactly what the general gluing theorem needs. The corrected proof applies that theorem directly and retains the intended construction and statement.

“Unique up to unique isomorphism” has its usual meaning for an object with the specified local identifications: the isomorphism must respect them. Step 5 spells this out. No uniqueness of a bare underlying scheme without these identifications is asserted or used.

## Review by Q46

I checked the proof against the above source text and opened every cited node to read its statement, rather than relying on its title or its proof. No new node needs a separate source review.

In step 1 the cited `lem-weil-pbc-open-preimage-fibre-product` states exactly that the inverse-image open subscheme is the fibre product with an open. Its hypotheses hold for a_i:P_i→Y and each covering open Y_j. The overlap maps preserve the base by hypothesis, so inverse images of Y_k match, and the triple cocycle with k=i yields the inverse relation. This supplies the domain condition needed for gluing; it does not assume affine intersections. This is an elementary verification from the cited statement and the datum.

In step 2 `lem-weil-pbc-glue-schemes` states existence of covering open chart maps, the exact intersection images, and the transition equation. Step 1 checks every hypothesis in its statement, including U_ii=P_i and the triple-domain equality. `lem-weil-pbc-scheme-morphism-gluing` states existence AND uniqueness for morphisms agreeing on the open overlaps. The maps a_i agree precisely because each transition is over the base intersection. Neither a definition of schemes nor an uncited quotient-existence assertion is being used for these theorems.

In step 3 the same gluing leaf supplies the covering and overlap equality used in the point argument. The cited definition `def-weil-open-immersion` explicitly says that an open immersion is an isomorphism onto its open subscheme. Thus once the displayed two-line inclusion argument shows q_i(P_i)=p^{-1}(Y_i), both schemes carry the restriction of the SAME structure sheaf on that open subset. This is why the topological equality suffices here; it would not suffice for arbitrary closed immersions. No hidden comparison lemma about unrelated subschemes is needed.

In step 4 the inverse-image fibre-product node gives the actual scheme pullback, not merely an equality on points. The definition of an open immersion gives cancellation of the base-open inclusion by its inverse on that open subscheme. Consequently the isomorphisms are over Y_i, and the chart equation from step 2 gives exactly phi_ij, with the correct direction, on the overlap. The elementary work here uses only the previously established chart equation and the two cited statements.

In step 5 the inverse-image node and open-immersion definition show that the second object's local charts are an open cover. The morphism-gluing node includes both gluing and equality detected on a cover. Apply it to q'_i q_i^{-1}; their overlap agreement follows from the shared phi_ij. Gluing the reverse maps and checking the two composites and the structure-map equality on each chart proves inverse, over-base and uniqueness clauses. I checked that the uniqueness claim is for isomorphisms compatible with the given local trivializations.

I tested a one-chart cover, disjoint base opens, repeated equal base opens with nonidentity transition automorphisms, empty P_i, and the empty cover of the empty scheme. The chart proof imposes no separatedness, finiteness, quasi-separatedness, affineness or nonemptiness hypothesis. In the empty-cover case the gluing theorem's covering conclusion forces P empty. The repeated-cover example is also the counterexample to the blueprint's source-map assertion.

Against delivery-errors B–E: there are no auxiliary nodes or duplicate clauses; the existing nodes are strictly general tools and their statements provide the exact facts used; all non-elementary facts are cited; each remaining elementary inference is written; source tags and labels are given; no cycle or off-route replacement is introduced. All five proof steps are below 2000 characters, so none conceals a long standard argument. The full statement is retained. The false proof sentence has been corrected, not reproduced.

## Not duplicates

No new nodes. `lem-weil-pbc-glue-schemes` is reused for abstract open-overlap gluing, `lem-weil-pbc-scheme-morphism-gluing` for the compatible-map universal property, and `lem-weil-pbc-open-preimage-fibre-product` for relative charts. The existing basis-indexed `lem-weil-pbc-relative-glueing-affine-opens` is not substituted for the arbitrary cover-cocycle assertion.
