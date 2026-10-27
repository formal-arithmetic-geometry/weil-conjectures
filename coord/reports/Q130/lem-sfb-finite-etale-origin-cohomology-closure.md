# Stage 1 report: lem-sfb-finite-etale-origin-cohomology-closure

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-etale-origin-cohomology-closure.json: statement, split; no Mathlib match.
- citations.json: verbatim statement extracts for all three step citations.
- report.md: worker report and signed self-review.

No new nodes; no Mathlib leaves. Existing statement, statement dependencies, source metadata, creation metadata and ancestry are preserved. The proof is three short steps (1388 characters total); every individual step is below 2000 characters. No unit record is changed: this is not the unit key node.

## Attachments

None claimed. I searched the exact blueprint tag and notions throughout lean/WeilConjectures. The project declaration AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_boundedConstructible at WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/Perfect.lean:386 has no sorry in its proof and works for any scheme and any finite commutative ring. Its boundedConstructible predicate is the map of the etale predicate under fixed-scalar ModuleCat-sheaf inverse image (Constructible.lean:93), rather than the item's intrinsic ring-sheaf comparison. Thus an encoding/derived comparison theorem is needed to use it for the literal item. I did not claim it as an exact attachment. The module-object theorem at ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean:106 instead has a NoetherianSpace hypothesis and a sorry, and is not an attachment. The intrinsic existing lemmas also have declarations in lean/Sheaf; the brief excludes those as direct project attachments.

## Wanted literature

None. No WANTED document and no forbidden SGA route.

## Findings and corrections

The item was unsplit, with no prior sandbox item or report and no repair note. Its statement is unchanged and no statement dispute is needed. Tag 09AL gives bounded-below derived comparison, which suffices for bounded objects, but the source definition-constructible is affine-local (proetale.tex:5225); one must not assert that this automatically equals a global finite stratification on arbitrary non-quasi-compact schemes. The proof therefore uses the statements of the existing globally stratified comparison and closure nodes. It never upgrades the original Stacks equivalence to an equivalence on all unbounded objects. The assembly is marked agent-written to make this global-convention specialization explicit.

All recorded searches added in this delivery were run via the required msearch.py command. searches.jsonl retains their exact results. I tried two LeanFinder phrasings, LeanSearch, Loogle and grep. LeanFinder returned scheme etale-category definitions or ordinary cohomological bounds; LeanSearch returned constant-sheaf images, localization triangles and ordinary derived bounds. Loogle returned ObjectProperty.instIsTriangulatedMapOfIsTriangulatedOfFull and two orthogonality results. I read Mathlib/CategoryTheory/Triangulated/Subcategory.lean:726 and :751: abstract essential-image closure needs a full functor and a triangulated source; it supplies neither the intrinsic coefficient comparison nor the constructible source. None is a one-line Mathlib proof of this item. Inherited searches in the live item are retained as historical records, not claimed as newly run by Q130.

## Not duplicates

No new nodes, hence no new/existing tag pairs. Searches of the whole DAG and blueprint for constructible closure, weak Serre, 09AL, 09AK and the item terms led to reusing lem-weil-pbc-finite-ring-constructible-derived-origin and lem-weil-proetale-dbc-triangulated rather than creating duplicates. blueprint_refs ancestor gives det-lem-int-integral-heart-triangulated. Existing same_as=[] and the precise from.place are retained. The first paragraph of that blueprint node's current proof uses exactly this finite-residue shift/cone stability. No unit route or chapter route is changed.

## Review by Q130

I read coord/delivery-errors.md B–E whole, the unit and chapter records, the exact item and its definition dependencies, the current blueprint integral-heart-triangulated proof, and Stacks proetale.tex lemma-compare-constructible-derived (09AL), lemma-constructible-serre (09B5), definition-constructible, plus derived.tex lemma-cohomology-in-serre-subcategory (06UQ) and the triangulated axioms (0145). No new-node source review is needed because no nodes were created.

For step 1 I opened the complete statement and proof of lem-weil-pbc-finite-ring-constructible-derived-origin. Its statement expressly uses the exact coefficient sheaves and termwise inverse image of def-weil-pbc-proetale-modules, arbitrary X and finite commutative B, global etale constructibility, and intrinsic pro-etale constructibility in a finite interval. Thus its essential-image assertion is precisely the iff needed, without a coefficient change hidden in the assembly. Its preservation/reflection of intervals also confirms boundedness. I read def-weil-pbc-constructible-complexes and both sheaf-constructibility definitions to verify that the finite partition is global in each. This step is non-elementary and cites the comparison, not merely a definition.

For step 2 I opened the complete statement and proof of lem-weil-proetale-dbc-triangulated. It expressly gives zero, isomorphisms, shifts in both directions and the outer-term triangle implication for intrinsic constructible cohomology on arbitrary schemes, over any finite commutative ring. These are all the conclusions this step takes. Its finite cohomological support is equivalent to existence of a finite integer interval: a finite set has min/max when nonempty, and the empty support uses [0,0]; conversely an integer interval is finite. Its intrinsic coefficient module category is the same one covered by step 1. This is a cited theorem invocation, not a purported elementary proof of constructibility. Both off-unit results are declared as generic tools in split_report.tool_uses.

For step 3 I opened def-weil-triangulated-category and copied its TR2 clause verbatim into citations.json. One and two forward rotations give respectively the first/two and last/two cases; the signs on the final morphism have no effect on the object predicate. Shift stability then removes [1]. This is a genuinely elementary deduction from the preceding closures and TR2, not a hidden cone comparison. Strict fullness is already part of the stated definition. Every cited quote was checked as an exact substring of its node's statement. The proof_deps list is exactly the union of uses. A transitive dependency traversal confirmed that neither closure/comparison theorem depends on this item, so the reuse creates no cycle.

I checked empty X (only the zero sheaf/complex), B=0 (the module category is zero), zero complexes, arbitrary positive and negative shifts, disjoint unions and non-quasi-compact schemes (no uniform finite stratification is inferred from local constructibility), and all three choices of two terms. Every theorem used permits zero rings and imposes no Noetherian, dimension or invertibility hypothesis on X. There is no new false small-case statement, no disguised restatement as a new node, no assumed full unbounded inverse image and no long step concealing another lemma. I corrected the provisional proof_origin from document to agent because Stacks' local constructibility convention is strictly weaker than this item's global convention on general schemes.

## Unfinished work

None for the authorized stage-1 split. Stage 2/3 proofs and compiles were not attempted. Final validation and push are performed with the required delivery tool.
