# Stage 1 report

Files written: item `lem-sbc-smooth-curve-points-decomposition` (statement, split); new statement nodes `lem-sbc-finite-clopen-connected-components` and `lem-sbc-zero-dimensional-smooth-point` (both unsplit, no Mathlib match).

Attachments: none.

WANTED: none.

## Review by NP

I read the imported item and its ancestor blueprint, the unit record, and the Stacks sources named in the item (etale-cohomology.tex Tag 0A5B, properties.tex Tags 033N and 0569, and varieties.tex Tag 06LH). I searched the Lean source trees for the item id and its geometric keywords; no declaration states it. I searched the DAG and blueprint for finite clopen component decomposition and for the zero-dimensional smooth point statement; no duplicate node states either fact. The first proof step cites the new finite-component statement, whose hypotheses are exactly finite type over a field and whose conclusion supplies finiteness, clopen inclusions, and the coproduct. The second step cites the new zero-dimensional point statement and the existing definitions of connected curves, open/closed immersions, and scheme coproducts; it checks that smoothness, separatedness, finite type, and the dimension bound pass to open-and-closed components, and that the two dimension cases exhaust the finite component set. I tested edge cases conceptually: the empty scheme gives empty index sets, a finite disjoint union of rational points gives only the J-family, and a connected smooth curve gives only the I-family. Mathlib searches were run for both new statements and recorded in their node files; LeanSearch was unavailable for the point statement and recorded as unavailable.

## Not duplicates

`lem-sbc-finite-clopen-connected-components` vs existing `lem-sc-regular-connected-integral`: the existing node concludes integrality of one connected regular scheme, while the new node gives finiteness and clopen decomposition of all components.
`lem-sbc-zero-dimensional-smooth-point` vs existing `lem-pc-dim-zero-finite-over-field`: the existing node requires properness and concludes finiteness/affineness, while the new node uses smoothness and connectedness to identify the scheme with Spec k.

lem-sbc-finite-clopen-connected-components vs def-weil-finite-type-morphism: the definition only defines finite type and does not assert component decomposition.
lem-sbc-finite-clopen-connected-components vs lem-pc-dim-base-change-affine-covers: that node concerns dimension under affine base change, not connected components.
lem-sbc-finite-clopen-connected-components vs lem-weil-pbc-qc-open-immersion-finite-type: that node concerns finite type of quasi-compact open immersions, not component decomposition.


## Second reading by NP

Item statement: checked Stacks 0A5B (etale-cohomology.tex, lemma-constant-smooth-statements) together with situation-what-to-prove at lines 15324–15327: algebraically closed field, separated finite type, dimension at most one, smoothness all agree; the component and immersion clauses express the stated disjoint-union reduction. Statement unchanged.
Step 1: checked lem-weil-pbc-finite-type-over-noetherian and lem-weil-pbc-noetherian-finite-components against Properties 0BA8 (lemma-Noetherian-irreducible-components) and Mathlib Noetherian.lean:364; field base satisfies Noetherianity, verdict pass.
Step 2: checked def-weil-irreducible-components and the Mathlib leaf lem-sc-irreducible-components-cover against Topology 004W (lemma-irreducible, parts 3–4) and lemma-Noetherian; the explicit finite intersection-graph argument proves connectedness and both openness and closedness, verdict pass (remaining argument elementary).
Step 3: checked the open/closed immersion definitions stalkwise, smooth-restrict-open-subschemes clause (a) against Morphisms 01V6 (lemma-smooth-characterize, final assertion), locally-finite-presentation and finite-type definitions, and closed-imm-base-change against the diagonal definition in def-weil-proper-morphism; finite polynomial presentations plus quasi-compactness give finite type, and the diagonal square has source C_a, verdict pass.
Step 4: checked lem-sc-smooth-regular against the smooth-curve definition (which explicitly allows dimension zero), its attached IsRegular.of_smooth declaration in Regular.lean:110–117, and regular-connected-integral against Properties 0569/033N and Regular.lean:220–227; nonemptiness is obtained from actual graph components and regularity holds by equal open-subscheme stalks; closed-subspace chains give dimension 0 or 1, verdict pass.
Step 5: checked zero-dim-integral-point verbatim against its integral, finite-type, algebraically closed and dimension-zero hypotheses and Varieties 06LH (lemma-algebraic-scheme-dim-0); scheme-coproduct-family supplies the disjoint open covering, and explicit glued inverse proves the isomorphism over k, verdict pass.
New node lem-sbc-finite-clopen-connected-components: checked its statement against Properties 033N/01T0; it is true for finite-type schemes over a field, but 033N assumes normality and does not state the asserted general fact, and 01T0 is a section rather than a lemma. Removed: its content is the elementary finite intersection-graph argument from existing component leaves, so no new node is needed (B5, C1, C2).
Previously reported new node lem-sbc-zero-dimensional-smooth-point: no such file remains in the received sandbox; confirmed the actual split already cites existing lem-weil-pbc-zero-dim-integral-point instead. No node recreated.

Changes: removed the unnecessary finite-component node; replaced the two compressed proof steps by five steps with the explicit graph, stalkwise closed immersion, inherited geometric hypotheses, dimension argument and inverse to the coproduct map; added missing citations for Noetherianity, component coverage, smooth restriction, regularity, closed-immersion base change, and definitions; regenerated citations.json from actual statements. Corrected stale split_report.summary and retained the first worker’s declared generic point-tool use in split_report for the maintainer to judge. No top-level tool_uses acceptance was written. The first worker’s Review by NP remains above as historical text; its two-new-node count is superseded by zero new nodes in this delivery.

Small cases: empty C gives an empty graph and I=J=empty; Spec k gives I empty and one J summand; a finite disjoint union of points gives only J; a connected smooth one-dimensional curve gives only I. A nodal connected reducible curve tests the general graph argument (the intersecting components give one connected union), but is excluded from the smooth item. Nonreduced Spec k[e]/(e²) is dimension zero and connected but not smooth or integral, so the point lemma is never applied to it.

Independent searches: msearch.py leanfinder “A Noetherian topological space is the disjoint union of finitely many clopen connected components” returned eight topology candidates, including isClopen_connectedComponent requiring locally connectedness; Loogle “\"NoetherianSpace\", \"connectedComponent\"” returned zero; grep “connectedComponent.*[Oo]pen|[Ff]inite.*[Cc]onnectedComponents” returned topology declarations requiring extra hypotheses, not a scheme decomposition. Actual outputs are in searches.jsonl. DAG searches by components/033N/01T0 located the existing finite irreducible components, component-cover, smooth-restriction, and integral-point nodes. The ancestor blueprint sbc-thm-algebraically-closed-invariance was read, as were the exact source statements cited above. No Lean was written or compiled.

Generic off-unit tool: lem-weil-pbc-zero-dim-integral-point is used solely to identify the dimension-zero integral components as Spec k; the unit has no such lemma. Other off-unit facts used here are existing Mathlib leaves or Lean-closed nodes and do not replace the unit’s route.

Delivery tooling: the instructed trailing “.” is rejected by deliver.py’s two-positional-argument parser (it prints usage); used the documented equivalent command without that surplus argument. First dry-run found the generic-tool declaration must remain under split_report.tool_uses; restored it and replaced plain arrows by TeX before rerunning.
