# Q60 stage-1 delivery: lem-sfb-nodal-graph-cone-fibre

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-graph-cone-fibre.json`: item, statement unchanged, status split; nine proof steps, all under 2000 characters. No new nodes and no Mathlib leaves.
- `citations.json`: one entry for every step/node citation, quoting the cited statement verbatim.
- `searches.jsonl`: actual msearch.py searches and results, retained in the sandbox. `prepare.py` is a sandbox-only preparation script.

## Attachments

None. I searched lean/WeilConjectures for the blueprint id, nodal/Nodal, graph conormal/graphCone, and associated graded/normalization comparisons. The few nodal occurrences are counterexample documentation or unrelated torsors. No declaration there states this item. The existing Sheaf nodal-local theorem is a statement with a postponed proof, and its DAG node is used as a lemma, not represented as a finished attachment.

## WANTED

None. All sources needed for the argument are available locally.

## Findings and corrections

The live item was unsplit, and the sandbox contained no previous split, report, citations, or search log. The statement is sound as written; no STATEMENT-DISPUTED correction was needed. The source is a local ring comparison followed by the intrinsic nodal tangent-normalization theorem, not a theorem that normalization of total spaces commutes with base change.

Several facts that might have become new nodes already exist. In particular `lem-sfb-nodal-local-tangent-normalization` supplies the exact intrinsic local Proj/normalization comparison (including branch interpretation and naturality). `lem-trf-separable-point-flat-completion-map`, specialized to K=F=kappa and the identity embedding, supplies the flat graph-local ring comparison and equality of maximal ideals. Its completed-ring conclusions are not used. `lem-weil-pbc-flat-iso-mod-ideal-powers` and `lem-sfb-power-quotient-graded-comparison` supply the remaining algebraic comparison. No node restating a clause of this item was created.

The item's hypotheses mention geometric pure dimension, while the existing tangent-normalization theorem requires ordinary pure dimension. Step 3 explicitly supplies that check from the existing local-dimension comparison and constant-local-dimension component criterion. It does not confuse local topological dimension with the dimension of a local ring.

The inherited `blueprint.from.node` is null: `python3 tools/blueprint_refs.py ancestor lem-sfb-nodal-graph-cone-fibre` returns None. The current import chain is broken above this created item. The existing descriptive place and via chain are retained, as those are not mine to replace. I read the current main-20261015 unit and its direct-images proof (3), as well as the stored chapter/unit records. This subargument remains the inherited branch input below the alteration route, and changes no chapter or unit. Whole-blueprint searches for nodal, tangent, normalization branches, associated graded, 0CBT, 0H1D, and flat associated graded found no equivalent imported blueprint node; the tangent hits concern different constructions.

## Not duplicates

No new nodes. All substantive inputs are reused. In particular the local tangent theorem has weaker scope than this item: it has no graph conormal algebra or global D-scheme assembly, and is therefore a proper dependency, not an attachment of this item.

## Mathlib searches read

I ran msearch.py leanfinder, loogle, grep and leansearch for this item, and a second leanfinder phrasing targeting the graph-local algebra comparison. The earlier searches in the copied live item are retained as historical records, not claimed as searches of this session. The new query texts and actual summaries were copied from this session's search log.

Loogle returns the relative normalization construction and its maps; I read the definitions and normalizationDesc in Mathlib/AlgebraicGeometry/Normalization.lean. These do not state the node's graph associated-graded comparison or nodal branch identification. LeanSearch returns analytic tangent cones and normalizationDesc, not algebraic nodal tangent cones. The first LeanFinder query returns Weierstrass nonsingularity declarations. The second returns residue-field separability and local unramifiedness criteria, not the graph-cone comparison. The Mathlib AlgebraicGeometry grep finds no nodal/conormal-normalization match. All new searches completed successfully. No Mathlib leaf is asserted.

## Review by Q60

I read Stacks curves.tex lemma-nodal-family (0C59), lemma-base-change-nodal-family (0C5B), lemma-nodal (0C4D), remark-quadratic-extension (0CBT), remark-trivial-quadratic-extension (0CBU), and lemma-split-node (0CBW). The remark explicitly omits an equivalence; that omitted equivalence is supplied here by the existing local tangent-normalization node, rather than claimed to be elementary. For the graph map I read varieties.tex lemma-change-fields-flat (0C4Y), lemma-change-fields-algebraic-unramified (0C50) and lemma-base-change-complete-local-ring (0C54), including its opening local-map and residue-square argument. I also read algebra.tex lemma-lift-basis (051H) for the flat quotient-power mechanism, and divisors.tex conormal-algebra-functorial and its flat version (0634/0635), along with the existing conormal node's affine/stalk formulas. Morphisms lemma-unramified-over-field (02G7) permits an arbitrary disjoint union, so there is no hidden finiteness restriction on D.

Step 1 uses the affine finite-type criterion, Noetherian finite-type implies finite-presentation, flatness over a field, and local Noetherian ascent. I opened each cited statement: the algebra statement is only applied to the Noetherian field k. The implication to locally finite presentation is its affine definition, and does not assume C is quasi-compact.

Step 2 uses exactly the support and unramified clauses of the nodal-family Fitting theorem. Step 1 verifies flatness and local finite presentation; the item supplies its geometric hypotheses. The unramified-field decomposition node explicitly allows an arbitrary index set and states finite separability. Closedness in C is justified by the finite-dimensional-domain argument in the text, not incorrectly inferred merely from closedness in D.

Step 3 uses the geometric-pure-fibre point-dimension node for a locally finitely presented map and the constant-local-dimension component criterion for a locally Noetherian scheme. Those hypotheses were checked in Step 1. It proves precisely the ordinary pure-dimension hypothesis used at Step 7. The empty scheme is harmless, as there are then no points or components to check.

Step 4 uses affine-pair finite type, the affine fibre-product tensor formula with its two projections, the open fibre-product identification, and the affine stalk-localization theorem. These statements identify the actual rings S_p and (S tensor kappa)_q. I wrote out why the latter is also a localization of A tensor kappa, why the graph ideal has quotient kappa, and why its inverse image is m. The graph is treated in an affine neighbourhood; no separatedness of the whole curve is used.

Step 5 uses only the uncompleted part of the separable-point flat-completion-map node. Its hypotheses are S finite type, p maximal with residue F finite separable, and an embedding F into K. Steps 2 and 4 verify these, and K=F with the identity embedding gives residue map identity and mH=J. The flat quotient-power node needs precisely flatness and an isomorphism modulo m, both now verified. The graded comparison node takes these actual quotient isomorphisms and proves the isomorphism on all homogeneous ideal-power quotients with the specified multiplication and naturality. I checked all three statements, not their proof sketches, for these clauses.

Step 6 uses graph-cone gluing and the conormal node's explicit stalk formula G_z=gr_J(R_z). Since D_x is an open field spectrum, the stalk and restriction equal the requested tensor fibre. This avoids using a general nonflat base-change theorem for conormal algebras. The isomorphism is the inverse of the actual degree-preserving map of Step 5.

Step 7 applies the existing local tangent-normalization theorem with all its hypotheses supplied in Steps 2--3, and uses the graded-iso Proj construction solely to projectivize the already-proved isomorphism. The local theorem explicitly states the normalization-fibre identification, separable quadratic alternatives, branch correspondence and naturality, so none of those facts is inferred just from a normalization definition. For the geometric algebra assertion, a split algebra stays split and a separable quadratic polynomial over an algebraically closed extension has two distinct roots. The branches remain unordered.

Step 8 uses the relative Proj definition only for its specified affine restriction maps. The gluing is elementary: the base opens are the pairwise disjoint D_x, so every overlap condition is empty, and both inverse identities are checked on these opens. This covers infinitely many singular points without any finite-cover assumption. Step 9 uses the explicit functoriality clauses of graph-cone gluing, the graded comparison, and the local tangent-normalization theorem. It checks the same augmentation square and homogeneous representatives, then invokes uniqueness of the disjoint-open gluing; it does not assert an unspecified compatibility.

I checked delivery-errors B--E against the final node: no new statement-only nodes are needed; every non-elementary input has a cited existing statement; every citation has a verbatim entry in citations.json; there is no SGA source or route change. I checked for a dependency path from the reused substantive nodes back to this item and found none. Small cases include empty/smooth curves (D empty), the split xy=0 node (two rational directions), a nonsplit separable quadratic node (one degree-two point), characteristic two (separability rather than a characteristic-not-two assumption), non-rational finite-separable nodes (the graph localizes the correct tensor factor), infinitely many components, and nonseparated curves. No argument assumes properness, connectedness, global finite type or finite D. Each proof step is below 2000 characters.

## Unfinished work

None within this one-level split. The reused unsplit lemmas remain their own DAG items; this delivery does not claim to prove their Lean statements.
