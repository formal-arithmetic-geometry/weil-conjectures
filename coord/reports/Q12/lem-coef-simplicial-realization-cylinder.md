# Stage-1 report: lem-coef-simplicial-realization-cylinder

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-realization-cylinder.json` — statement unchanged; four proof steps, searched against Mathlib; status split.
- `citations.json` — verbatim statements for every node used in steps 1 and 3.

There are 0 new nodes and 0 new Mathlib leaves. The earlier attempt's uncommitted `lem-coef-kspace-product-compact-factor.json` was removed from the sandbox: its required interval case is a short consequence of existing statements and is now proved in step 3. No repository node was deleted or edited.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the read-only master source for the item tag, cylinder realization, geometric realization, and `toTop` found no declaration giving the item. The master checkout was used only as reference material. Mathlib's standard-simplex homeomorphism gives only the second factor, and the `hoFunctor` product theorems concern a functor to categories, not geometric realization.

## WANTED

WANTED: an archived copy under `literature/` of Hovey, *Model Categories*, Lemma 3.1.8, printed pp. 77–78, its following discussion on p. 79, Definition 2.4.21 and Proposition 2.4.22, printed p. 58, and the locally compact exponential-law discussion in §2.4, printed p. 49, for this item. I read the PDF online at the item's recorded URL; I did not download it or write into `literature/`. The proof origin is agent, since the explicit interval quotient and ordinary-product passage are supplied here and the PDF is not archived locally. Lewis's Appendix is no longer needed by this split.

## Problems found and corrections

The old report claimed a passed dry run without providing a reproducible result for this reading. It also described Hovey's proposition on k-ified limits as if it directly stated the compact-factor product theorem. I replaced that unsupported source attribution with an explicit compact-test argument using the existing Mathlib currying leaf. The old supporting node cited the k-space node in its statement but omitted it from `stmt_deps`; eliminating that redundant new node also removes this defect.

The old interval argument separated constant simplices without spelling out their relation to the identity simplex. Step 2 now applies the quotient relation directly to every monotone map to [1], constants included, and checks invariance under every simplicial operator by associativity of coordinate sums. Source labels that asserted Hovey explicitly proved the endpoint formulas were corrected: these are our representative calculations. The item statement itself has no dispute or correction.

## Not duplicates

No new nodes remain. I searched `dag/nodes/` and the whole imported blueprint with `tools/blueprint_refs.py` for realization, cylinder, compact-open, and compact-factor product terminology. The existing `lem-coef-realization-finite-limits` supplies the k-product comparison; the existing `lem-coef-compact-open-currying` supplies the only remaining non-elementary topological operations. Both are in the same chapter and unit as this item, so no off-unit tool declaration is needed.

## Review by Q12

I read the worker contract, stage-1 rules, SETUP's three levels, GOAL, DAG-sync rules and delivery-errors B–E; the chapter `sec-six-functors`, the unit `sk-prop-sf-biduality-general`, the item's ancestry and `prop-coef-integral-exceptional-adjoint` proof; the item; and the complete statements of both cited nodes. I also read Hovey's Lemma 3.1.8 and its k-space warning online, together with Definition 2.4.21 and Proposition 2.4.22. They justify keeping the finite-product comparison in k-spaces and explicitly proving the ordinary-product transition. This is a tool below the unit route and changes no unit or target statement.

Step 1 uses precisely the clauses of `lem-coef-realization-finite-limits` saying that realization takes values in k-spaces, preserves finite limits naturally, and that k-space limits are k-ifications of ordinary limits. The hypotheses are arbitrary small simplicial sets, so K and the standard interval qualify without any finiteness or Kan hypothesis. The representative formula follows from the two projections. The realization defined in the item is the same quotient realization, with the same affine maps, as in that node's cited conventions.

Step 2 uses no lemma: the coordinate sums respect each defining relation, and the relation associated to theta gives the continuous inverse directly. This treats theta constant at 0 or 1 and allows zero barycentric coordinates. Thus it does not silently discard boundary classes or reverse the two endpoints.

Step 3 uses the final compact-test definition and k-ified product convention from `lem-coef-realization-finite-limits`, and both directions of `lem-coef-compact-open-currying`. I read that leaf's full statement and Mathlib/Topology/CompactOpen.lean:430–467: currying maps a continuous A×I-family into the compact-open mapping space; uncurrying requires local compactness only of I. Every compact Hausdorff test A has compact Hausdorff A×I, so its product map lifts continuously into the k-ification by the definition of that topology. The final topology on X then proves continuity of G, and uncurrying proves continuity of the inverse identity. No compactness or local compactness of |K| is assumed. The interval's compact neighbourhoods work also at 0 and 1. These are the exact hypotheses used; no weak-Hausdorff or separation hypothesis on X is added.

Step 4 uses the previous steps and the representative formula: the two naturality composites agree on every representative, while the constant endpoint labels give sum 0 or sum 1. It is elementary and introduces no new topological theorem.

I tested K empty (both cylinders empty), K the point (the interval identification), arbitrary discrete K (a disjoint union of intervals), and the identity and constant interval simplices. The argument also permits infinite K because compact tests replace any local compactness assumption. Every cited node is unmerged, in the same unit, and the new edges point to existing supporting nodes rather than back to the item. All proof dependencies equal the union of step uses. The statement and its sole statement dependency are unchanged; no hollow definition, new Lean file, compiler invocation, forbidden SGA route, or target edit is involved.

All added Mathlib records are actual `msearch.py` calls and use the exact query strings in `searches.jsonl`. I repeated the item search in two semantic phrasings, used Loogle including a fully qualified product-comparison query, and read the returned standard-simplex and categorical-homotopy hits. `TopAdj.lean` has the standard-simplex homeomorphism but no arbitrary-cylinder product theorem. No new Mathlib leaf is claimed.

## What could not be finished

No mathematical gap remains in this one-level split. The required remote `deliver.py Q12 lem-coef-simplicial-realization-cylinder --no-push .` dry run is the final validation step; READY is issued only if it prints OK. The sandbox is for a fresh second reader, who alone delivers it.

## Second reading by Q12

- Item statement: checked every hypothesis and the quotient formula against Hovey, *Model Categories*, Lemma 3.1.8, printed pp. 77–78, and the k-space warning on p. 79; PASS. The ordinary interval product is justified by Step 3, with no finiteness, Kan, or local compactness hypothesis on K. Stacks `simplicial.tex`, labels `section-simplicial-set` (0174), `definition-terminology-simplicial-sets` (0175), and `example-simplex-simplicial-set` agree with the simplicial-set and representable conventions. There is no Stacks tag for this topological theorem.
- Step 1: checked the complete statement of `lem-coef-realization-finite-limits`, its quotient-realization convention in `def-cbc-enhanced-diagrams-cones`, and Hovey Lemma 3.1.8 / Proposition 2.4.22(3); PASS. Only the k-space and natural product clauses are used, for arbitrary small simplicial sets. Projection formulas determine the representative map.
- Step 2: checked directly against the item's defining equivalence relation and the affine coordinate sums; PASS. Associativity of finite sums proves invariance, and the relation for theta identifies every representative with the identity 1-simplex, including both constants and zero weights. Both inverse maps are continuous on the relevant simplex or quotient.
- Step 3: checked the complete statements of both cited nodes, Hovey Definition 2.4.21 and Proposition 2.4.22(3), and Mathlib `Topology/CompactOpen.lean:430–467`; PASS after explicit compact-test inverse-image and finite-product compactness explanations. Currying and uncurrying are applied with the locally compact interval as their source. No separation condition on X or Z is used.
- Step 4: checked the formula from Steps 1–3 on all representatives and both constant endpoint simplices; PASS after spelling out the homeomorphism induced on k-products by e and its inverse. Both naturality composites agree pointwise, and the endpoint sums are 0 and 1.
- New nodes: none; PASS on B1–B7 and the duplicate/restatement/elementary-node checks vacuously. Both supporting nodes already exist in the item's unit; the compact-open node is a Mathlib leaf, and the realization node states a broader finite-limit theorem, not this item's conclusion. The split introduces no off-unit tool citation.

Small cases checked independently: empty K (both spaces empty), terminal K (the explicit interval inverse), a discrete set of vertices (one interval per vertex), n = 0 and n = 1 representatives, constant interval labels, and vanishing barycentric weights. All satisfy the stated formula and both endpoint identifications. Infinite K is permitted throughout: compactness is required only of the test parameter and the interval. The natural statement and its statement dependencies match the shared item verbatim; no statement dispute was found.

I checked the chapter/unit records and the ancestor's derived coefficient adjunction step. This remains a topological tool below that route; neither the unit nor any target changes. Searches by item id and realization/cylinder/toTop vocabulary in the read-only slopmaster2 and master sources found no matching declaration (the absent master Comparator directory was not treated as evidence). The master source supplies no finished-proof claim. Fresh `msearch.py` LeanFinder, Loogle and grep queries are recorded verbatim in `searches.jsonl` and the item's `mathlib_searches`; their hits state the standard-simplex identification, categorical homotopy-functor product preservation, or fundamental-groupoid results, not this cylinder homeomorphism. I read `TopAdj.lean:164–171` and `NerveAdjunction.lean:471–484` to distinguish them.

Changes made in this second reading:

- Step 3 now gives the inverse-image reason compact tests lift to k-ification, to make the topology argument directly checkable.
- Step 3 now supplies the finite rectangle-cover proof that A times I is compact and the coordinate-separation proof that it is Hausdorff, avoiding an implicit topological input.
- Step 4 now writes the induced k-product homeomorphism and its inverse by their projections, avoiding an unexplained passage between product topologies.
- Added three actual independent Mathlib search records; kept all previous search records and the author's `## Review by Q12` intact.
- Validated all three citations against the exact current supporting statements and checked that they cover exactly the step uses. Their text needs no change.

There are still 0 new nodes and 0 new Mathlib leaves. Only sandbox files were edited; no Lean or compiler/build tool was used. The required server dry run and delivery follow this reading.

Required dry run completed: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q12 lem-coef-simplicial-realization-cylinder --no-push .` exited 0 and printed `OK (not pushed) deliver/Q12/lem-coef-simplicial-realization-cylinder at 99c6f52479: preflight passed`. All checks ran through the delivery tool on the server; none of the prohibited preflight/check scripts was run locally.
