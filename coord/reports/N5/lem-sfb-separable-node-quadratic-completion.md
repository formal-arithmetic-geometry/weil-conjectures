# Stage 1 report: lem-sfb-separable-node-quadratic-completion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-separable-node-quadratic-completion.json`: statement, split in nine steps; no Mathlib match. Preserved the original statement, source, creation record, blueprint provenance, and earlier searches. Added the missing definition citation for equidimensionality, without changing its meaning.
- No new nodes; no new Mathlib leaves. All prerequisites already have nodes.
- `citations.json`: 27 step/node entries, quoting the cited statements verbatim (whole statements where several clauses are used).
- `searches.jsonl`: actual N5 search-command results. `write_split.py` is sandbox-only preparation material.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for nodal/ordinary-double-point/quadratic-completion terminology. No declaration there states all clauses. General occurrences concern unrelated six-functor constructions or locally constant sheaves. Existing declarations recorded on the reused trace-formula nodes do not attach this item; their statements are used through their DAG nodes.

## Wanted sources

None. All sources used are present under `literature/stacks-project/`.

## Findings and repairs

The imported statement is correct. The rational-residue-field node `lem-trf-rational-node-quadratic-completion` does not apply directly: here the residue field is a finite separable extension of the ground field, not necessarily equal to it. Instead I use the existing general separable closed-point formal-presentation theorem, retaining its actual coefficient section, and the existing formal Jacobian criterion over that residue field. No new rational-to-nonrational restatement node is needed.

The original item lacked a definition citation for pure dimension. I added `def-weil-pure-dimension` while retaining its Krull-dimension reference. There is no strengthened hypothesis and no weakened conclusion. Its blueprint ancestor is genuinely null according to `tools/blueprint_refs.py ancestor`; I preserved the detailed existing `from.place` and `via` chain. Whole-blueprint searches for `nodal` and `quadratic` found no imported equivalents. The existing general Jacobian, formal-presentation and depth tools are declared in `split_report.tool_uses` where their units differ, because they are local algebra tools below the unit's alteration route, not a replacement route.

## Not duplicates

No nodes created. The rational-node completion node is strictly narrower in its residue-field hypothesis. The general formal Jacobian criterion is an existing tool that requires a formal presentation, depth one and a maximal Jacobian minor ideal; steps 1–7 establish those inputs here. The separable closed-point formal-presentation node supplies presentation and comparison data, not the quadratic normal form. Neither is copied or restated as a new node.

## Review by N5

I read the item against Stacks `curves.tex` Tags 0C4D (`lemma-nodal`), 0C4C (`lemma-fitting-ideal`), and 0C49 (`lemma-nodal-algebraic`), including the arbitrary-field descent and successive-correction arguments. I also read `varieties.tex` Tags 0C52/0C54 and the flat/unramified field-change lemmas 0C4Y/0C50, and `more-algebra.tex` Tag 0C34 for the coefficient section. These sources justify the use of the actual separable residue field rather than silently making the point rational over k. There are no new nodes whose sources need a separate review.

For step 1 I opened the finite-type affine-pairs node, the affine-open stalk-localization node, and the essentially-finite-type definition: they give respectively finite generation of S, the actual localization A=S_p with its germ map, and the definition applied to S minus p. For step 2 I opened the affine fibre-product node, geometric-field-stalk-descent node, and separable closed-point formal-presentation node. The first identifies the actual chosen geometric point in the tensor-product spectrum; the second explicitly gives that its residue field is the structural algebraic closure K. The residue map therefore determines the embedding kappa into K and its evaluation kernel q. The third explicitly states all the required Noetherian/local/completion/coefficient-section/Jacobian comparison assertions, for any presentation. Its finite separable residue hypothesis holds by the item's assumption. Its second application is to S tensor K over K at q, with residue extension K/K, so it supplies the same facts for B and its completion. No conclusion is borrowed from a node's proof.

For step 3 the equidimensional-open local-dimension node is applied to the whole C, not to an open assumed equidimensional without proof. The open-subspace dimension node passes this value to U; the closed-point local-dimension node applies because S is finite type over a field and p is maximal. I read Tag 0A21 and algebra Tag 00OU for these hypotheses.

For step 4 I opened both differential comparison nodes, the differential definition, and the Fitting-ideal node. The finite generation calculation is written using the symbols/Leibniz definition and then localization. The cited comparison statements really identify the localized differential modules, and Fitting clause (2) gives extension of ideals. I read algebra Tags 00RT and 00RV and more-algebra Tags 07Z8 and 07ZA(3). Step 5 uses the Jacobian cokernel clause of the formal-presentation node and implication (c) to (a) of the formal Jacobian criterion. Its condition (c) explicitly permits an abstract ring isomorphism: I did not presume that the hypothesis's ring isomorphism is K-linear. The split model has a=c=0 and b=1. Fitting presentation independence and base change then give the extended first Fitting ideal. The comparison between finite relation rows and arbitrary kernel rows is the displayed multilinear determinant expansion, not a further unnamed lemma.

For step 6 I opened the completion faithful-flatness and ideal-contraction statements and read algebra Tags 00MC and 05CK. Each ring completed is Noetherian local by step 2. Equality of extended maximal ideals in that step is essential to the second contraction; it is explicitly part of the cited statement. For step 7 I opened the flat local depth-formula node and depth definition and read algebra Tag 0337. All three maps are flat local maps of Noetherian local rings, their closed fibres are the fields stated in step 2, and fields have depth zero from the definition. This gives depth of A and its completion without assuming reducedness or dimension suffices for depth.

Step 8 again uses the explicit Jacobian-cokernel, Fitting and formal-criterion statements, this time over kappa with the coefficient section already chosen. Its nonzero discriminant and complete local kappa-algebra isomorphism are exactly condition (b). The proof separately checks the residue identity by constants and continuity by equality of powers of maximal ideals. Step 9 does not assert that a general quotient of a reduced ring is reduced. I wrote the two substitutions on the split nodal quotient, computed their common kernel coefficient by coefficient, and used only the domain clause of the existing power-series-ring node with one variable. The ideal-contraction statement explicitly gives injectivity at the zero ideal, so reducedness descends along the two injective maps already constructed. This is the elementary coefficient argument in 0C49's reducedness paragraph, expanded rather than promoted to a new node.

Small-case checks: the split model uv works over every field, including characteristic two, since b squared minus 4ac equals 1. A nonsplit quadratic node over R remains allowed; the proof never asks for two rational branches. A nonrational point with finite separable residue field keeps kappa throughout the coefficient section and final isomorphism. No characteristic-not-two assumption is used: the polar matrix criterion already includes characteristic two. Smooth points and double lines fail the geometric nodal hypothesis and are not falsely included. An empty curve supplies no closed point, so the statement is vacuous there. Nilpotents are excluded by the explicit injection into the reduced split completed ring.

I checked delivery-errors B–E: every object and hypothesis in the reused statements is in force; each definition citation defines the notion it labels; no new nodes relabel a clause; no tags replace dependency nodes; proofs use statements rather than proofs; all uses equal the union recorded in proof_deps; all citations quote those statements literally. I checked the dependency closures of the principal reused tools for a path back to this item and found none. Every proof step is below 2000 characters, and I checked that none hides a separate comparison. New-node search/duplicate/leaf-line obligations are vacuous. The item's six fresh searches were run with the mandated command (two semantic phrasings, Loogle, LeanSearch, and grep in both AlgebraicGeometry and RingTheory); all services answered, and none states this theorem. Weierstrass division and elliptic-curve reduction hits are not node-completion classification.

## Unfinished work

None in the stage 1 split. The required server dry run and delivery follow this report. This delivery writes no Lean and runs no compiler or build tool.
