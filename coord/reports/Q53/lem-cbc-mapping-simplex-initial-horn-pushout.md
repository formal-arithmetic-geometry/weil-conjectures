# Q53 — lem-cbc-mapping-simplex-initial-horn-pushout

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-mapping-simplex-initial-horn-pushout.json`: statement node, now split into six elementary coordinate checks. No full Mathlib match.
- `citations.json`: eleven step/node records with verbatim excerpts from the three existing cited statements.
- `searches.jsonl`: actual output records from the required search wrapper, retained without edits.
- `report.md`: this report. `write_split.py` is sandbox-only preparation material, not a DAG delivery.

New nodes: 0. New Mathlib leaves: 0. The original statement, statement dependencies, source, creation metadata and historical blueprint provenance are preserved. Existing Mathlib search records are retained and the five searches of this worker are appended.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id and for mapping-simplex and initial-horn spellings. There is no matching project declaration. The absence of an attachment does not rely on the upstream master's sorry declarations.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Section 3.2.2, printed p. 179 (mapping-simplex definition and Notation 3.2.2.3), and Corollary 3.2.2.12 with proof, printed pp. 185–187, for lem-cbc-mapping-simplex-initial-horn-pushout. Read the official IAS PDF online at https://www.math.ias.edu/~lurie/papers/HTT.pdf, PDF pages 197 and 203–205 (one based). No copy was downloaded or written into the shared repository. The proof is marked agent-written. There is no Stacks tag for this particular marked simplicial construction, and no SGA source is used.

## Input issues and corrections

No statement dispute was found. The input had an empty proof; the source's reduction of the mapping problem for i<n is not by itself a proof of the asserted universal property with selected markings. The split now supplies that property by an explicit piecewise extension. In particular it checks operators that take a simplex outside the horn into the horn, and checks that every marked edge is the image of a marked edge of a pushout piece. It does not infer a marked pushout merely from an unmarked one.

The name M^m(A) is used for the underlying mapping-simplex construction with the marking explicitly prescribed by this item. That marking is restricted by the base set T_n, whereas the generic mapping-simplex node marks all edges whose second coordinate is degenerate. The statement itself explicitly makes this replacement; the proof uses exactly the restricted marking, not the generic marking or any model-category theorem.

The item is an auxiliary created node, not the statement of its unit. Its historical blueprint ancestor is thm-cbc-finite-level-proetale; the current main-20261015 proof opens with the compactification choice. The present coordinate lemma realizes the last-cylinder gluing in steps 4–5 of lem-cbc-enhanced-relative-exponential through the recorded chain of auxiliary splits. Neither unit realization fields nor chapter/unit metadata need changing.

## Searches and reuse

Searched the whole DAG for mapping-simplex, initial-horn and pushout phrases, and the whole imported blueprint with `tools/blueprint_refs.py search` for `mapping simplex`, `initial horn` and `pushout`; the first two returned no blueprint matches, and the pushout matches concern sheaves or additive group schemes. Read the related initial-prism filtration, mapping-simplex universal-equivalence and marked-descent statements: they assert different results. No new node is needed, so there are no new/existing node pairs for duplicate comparison.

Ran LeanFinder with two distinct formulations, Loogle with `"SSet", "IsPushout"`, LeanSearch with the cylinder/horn formulation and the recorded Mathlib grep. All services returned successfully. Read the returned results and Mathlib `SubcomplexColimits.lean:86` and `HornColimits.lean:54` (with the adjacent horn statements). The former asserts the unmarked pushout of four subcomplex inclusions. It is not a one-line specialization to this item: c_K can identify different simplices when chain transitions are noninjective, and the selected marked-edge conclusion is additional. The horn pushouts glue edges to form ordinary two-dimensional horns, not mapping simplices. Generic cylinders and horn generators do not state this result. Consequently the item is not a Mathlib leaf. No searches were invented, and no compiler, Lake or Lean-building tool was invoked.

## Not duplicates

No new nodes were created. In particular the definition-level complement-of-horn calculation and the direct universal-property verification remain proof steps, rather than new lemmas restating clauses of the item.

## Review by Q53

I read the standing stage-1 brief, stages/1-dag.md, SETUP.md's chapter/unit/node hierarchy, GOAL.md, coord/dag-sync.md, the worker role, the chapter and unit records, and sections B–E of coord/delivery-errors.md. I read HTT's actual mapping-simplex coordinate definition and the reduction at the end of the proof of Corollary 3.2.2.12 in the official PDF, not just the node's source label. Since the book is not archived locally and the restricted markings and detailed extension formula are written here, proof_origin is agent. There are no new nodes needing separate sources or searches.

For step 1 I opened lem-coef-cartesian-mapping-simplex-presentation and used precisely its statement giving the operator on the second coordinate. The equality is composition of the chain transitions and naturality of those transitions as simplicial maps. I also opened lem-coef-marked-point-cartesian-model and used only its definitions of a marked object, marked map, minimal marking and product marking. The proof writes a marked cylinder edge as (s_0 b,alpha), so its image is marked for exactly the selected base edges. It checks that the new marking contains the degeneracies. No Cartesian-fibration property is assumed for a mapping simplex.

For step 2 I opened def-cbc-enhanced-diagrams-cones and used its exact definition of the horn as the maps omitting some vertex other than 0. Its negation forces n into the image, and monotonicity puts n at the last vertex. This establishes the unique cylinder representative outside the horn directly. In particular this uses n>=1, not an unstated surjectivity hypothesis on any transition map.

For step 3 the same two cited statements supply the degreewise pullback and the types of the simplex coordinates. I checked the two branches of h are well-typed, that the outside branch really has a in A_n, and that compatibility on A_n times K proves h c=v even when c_K has multiple preimages. There is no invocation of an unproved theorem about colimits of presheaves or marked objects.

For step 4 the cited simplex, pullback and mapping-simplex operator statements suffice. The equations in the node verify naturality on the horn piece and on a cylinder representative, separately. The identity h c=v was proved as an equality of functions in every degree before it was used here; no circular assumption that h is already simplicial is made. Operators whose last vertex changes and whose image enters the horn are covered by the same equation.

For step 5 the existing marked-object/product statement says exactly what is needed to lift every marked edge to a marked edge in a piece. On the horn the induced marking suffices; outside it the second coordinate is in A_n and is degenerate, so the cylinder edge is marked. Equality on all simplices then gives uniqueness. The universal property proved is for arbitrary marked Z, with no fibrancy, Kan, small-colimit existence or quasicategory hypotheses.

For step 6 I rechecked the horn definition with n=1: it consists of constant maps at 0, and the restricted fiber is A_0 with minimal marking. I checked n=2: the missing edge is [1,2], whose coordinate belongs to A_2, while [0,1] is in the horn, as the selected-marking test requires. For n>=3 every edge lies in the horn, although higher simplices may lie outside; the degreewise proof still applies. If A_n is empty, all outside-horn simplices are absent, and the formulas do not choose an element of an empty set. An empty earlier term forces the later terms mapping into it to be empty; no impossible chain was silently used. A noninjective collapse A_1 -> A_0 in the n=1 cylinder identifies multiple horn representatives, and step 3 still gives a unique extension because of the imposed compatibility. These small cases also show why the inclusion-only Mathlib pushout theorem is not an exact match.

I checked B's self-containment and definition citations, C1/C4's exact statement use and coverage, D's ban on moving the result to a new node, and E's missing hypotheses, wrong-object and hidden-transport pitfalls. All six steps are short direct substitutions or case checks from the cited definitions; none invokes an independent non-elementary result. Each has elementary=true and an explicit argument, rather than merely calling it obvious. Step lengths are below 800 characters, so none triggers the >2000-character hidden-lemma check. citations.json contains a verbatim statement excerpt for every step/node pair. The only off-unit uses are the generic explicit mapping-simplex and marking definitions; split_report.tool_uses explains them without changing maintainer-owned tool_uses.

I rechecked this retained delivery against the current shared snapshot on 2026-10-17. Only the intended split fields differ from the current item; its statement and provenance still agree. The current parent uses this result in step 5 after setting up its objects in step 4. I also read the newer lem-coef-mapping-simplex-last-fiber-pushout: it is an unmarked attachment along the final face, whereas this item attaches along the initial horn with specified markings, so it does not replace this statement. I tightened the step-3 citation excerpts to the actual degreewise-coordinate and pullback clauses, and the step-6 excerpt to the vertex-fiber clause. All eleven excerpts remain verbatim parts of the current cited statements. I reread HTT printed pp. 179 and 185–187 and the recorded Mathlib candidates; no new search question or statement change required repeating the retained searches.

## Unfinished work

None in the split. The existing dependency nodes remain as they were; this item does not need their model-structure or equivalence claims.

## Validation

The first resumed dry run rejected the shortened step-6 vertex-fiber quotation because it was below the required 40-character minimum. Expanded it to include the adjacent marking clause, still verbatim from the same statement. The subsequent dry run and direct delivery determine the final result.

The next resumed dry run completed the fetch and server queue but rejected step 3 under B4: the TeX cases row separator immediately before v_r matched the doubled-backslash check. Replaced the cases environment with the same two inline equations and conditions. This changes only the rendering, preserves the complete piecewise extension proof and all citations, and leaves the statement unchanged. Rechecked all eleven verbatim citation excerpts against the current dependency statements and all six step lengths (each below 800 characters). No new Mathlib search question arose.
