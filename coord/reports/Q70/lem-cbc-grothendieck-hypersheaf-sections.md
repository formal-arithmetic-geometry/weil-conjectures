# Stage-1 report: lem-cbc-grothendieck-hypersheaf-sections

Files written:

- `dag/nodes/sec-smooth-purity/lem-cbc-grothendieck-hypersheaf-sections.json`: statement retained in the corrected form with the local lower-refinement hypothesis; split into five proof steps.
- `dag/nodes/sec-smooth-purity/lem-cbc-grothendieck-presheaf-coherent-straightening.json`: statement-only auxiliary foundation; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-cbc-grothendieck-hyperdescent-local-refinement.json`: statement-only auxiliary foundation; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-cbc-grothendieck-coherent-end.json`: statement-only auxiliary foundation; no Mathlib match.
- `citations.json`: verbatim statement quotations for every proof-step citation.

The target node was absent from the read-only DAG snapshot. I reconstructed the exact corrected statement from the prior stage-1 record in the launcher logs; the reconstructed file is therefore a new overlay node for delivery.

Attachments: none. Searches of both Lean source trees by the item tag, hypersheaf terminology, and coherent/Grothendieck-section terminology found no project declaration without `sorry` stating the item or any auxiliary foundation.

WANTED: an enhanced presheaf straightening/Fubini theorem for a Grothendieck construction of full-sieve sites, for `lem-cbc-grothendieck-presheaf-coherent-straightening`.
WANTED: a hyperdescent comparison for the generated total-site topology under local lower refinements, for `lem-cbc-grothendieck-hyperdescent-local-refinement`.
WANTED: an enriched coherent-end theorem identifying derived mapping complexes on the total site with fibrewise coherent systems, for `lem-cbc-grothendieck-coherent-end`.

## Source error

The earlier unrestricted formulation omitted local lower refinements and is false. Take a branching poset with arrows i<k and j<k but no common lower index, and let every fibre be the one-object category with trivial topology and every transition the identity. The generated total topology forces the value at the j-fibre to vanish after pulling back the singleton cover i→k, whereas the homotopy limit of the constant fibre categories is nonzero. The corrected statement adds the explicit local lower-refinement condition. In the geometric basis application, an arrow between charts over U and V is covered by inverse images over basis opens Z⊂U∩V, whose labels lie below both endpoints; this verifies the added condition without requiring U∩V itself to be a basis object.

## Review by Q70

I read the current `thm-cbc-finite-level-proetale.proof.md` opening compactification paragraph and the prior imported record containing this node. I checked that the target introduces all site, hypersheaf, enhanced-derived, and lower-bound notions it uses, and that its statement keeps the exact fibrewise coefficient category and transition direction. I also read the existing definitions `def-weil-size-convention`, `def-weil-abstract-derived-category`, and `def-cbc-enhanced-diagrams-cones`; step 1 cites only those definitions and records the unpacking as elementary.

For step 2 I read the new straightening statement itself: it supplies the presheaf restriction/inversion equivalence and the coherent transition data used by the step. For step 3 I read the new local-refinement statement itself: it supplies both directions of the total-versus-fibre hypersheaf criterion and preservation of the lower bound. For step 4 I read the coherent-end statement itself: it supplies the derived mapping-complex identification, naturality, identities, and composition. Step 5 uses exactly these three statements to obtain naturality under subposet restriction and compatible diagram maps. Every quotation in `citations.json` is copied verbatim from the cited statement; no step relies on a proof hidden inside a cited node.

I tested the corrected local-refinement hypothesis on the branching-span counterexample above and on the intended etale basis diagram. The unrestricted version failed the span test and was replaced before writing the item. All three auxiliary statements are strictly smaller foundations and carry no proof sketch, no Stacks tag, and no Mathlib declaration claim. The Mathlib searches were run with `msearch.py` and recorded in `searches.jsonl`; ordinary Grothendieck constructions, one-step hypercovers, and presheaf Hom/end APIs were inspected and found insufficient for these enhanced statements.

What could not be finished: the three WANTED foundations have no supplied literature proof and no Mathlib match, so they remain statement-only unsplit nodes for later work. No Lean was written or compiled, as required for stage 1.

## STATEMENT-DISPUTED
The worker's auxiliary straightening statement was false as originally written: for the span $I=(0<1)$ with both fibres terminal and target $mathbf{Set}$, a presheaf on the total category is an arbitrary map of sets, whereas a coherent fibre system requires that map to be a bijection. I repaired the statement to the full subcategory of presheaves that invert every identity-underlying transition arrow; the target's presheaf clause was corrected in parallel.

## Second reading by Q70

- Step 1 checked the site, topology, size, enhanced-target, and lower-bound definitions in the item and cited nodes; verdict: elementary unpacking.
- Step 2 checked against `lem-cbc-grothendieck-presheaf-coherent-straightening`; verdict: repaired to apply only to presheaves inverting transition arrows, with the inverse arrow formula written explicitly.
- Step 3 checked against `lem-cbc-grothendieck-hyperdescent-local-refinement`; verdict: repaired to identify vertical hypercovers and singleton covers and to state how local lower refinements handle mixed arrows.
- Step 4 checked against `lem-cbc-grothendieck-coherent-end`; verdict: repaired to use the coherent/inverting presheaf category and to spell out the restriction of arrow strings.
- Step 5 checked against all three auxiliary statements; verdict: marked non-elementary and states the restriction/naturality operations explicitly.
- `lem-cbc-grothendieck-presheaf-coherent-straightening` checked for self-contained $\mathcal E$, strictness, full-sieve meaning, and the invertible-transition subcategory; verdict: corrected false unrestricted claim.
- `lem-cbc-grothendieck-hyperdescent-local-refinement` checked for self-contained $\mathcal E$, topology, local lower-refinement, coherent presheaf, and lower-bound meaning; verdict: corrected and made self-contained.
- `lem-cbc-grothendieck-coherent-end` checked for self-contained $\mathcal E$ and coherent presheaf hypotheses; verdict: corrected to the inverting-transition category.

Changes made: added the sheafification definition dependency and citation; defined coherent presheaves in the target; corrected the three auxiliary statements and the target's presheaf comparison; rewrote steps 2--5 to avoid hidden proof use and vague transport language; marked the naturality step non-elementary; regenerated verbatim citation quotations. The branching-span counterexample above is the edge-case test for the repaired statement. No Stacks tag is supplied for this enhanced categorical infrastructure, and no Lean or compiler tool was run.
