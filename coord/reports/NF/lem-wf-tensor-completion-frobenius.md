# Stage-1 worker report: lem-wf-tensor-completion-frobenius

## Files written

- `dag/nodes/sec-six-functors/lem-wf-tensor-completion-frobenius.json` — statement node, no new nodes, no Mathlib leaves. The item keeps its statement and now has five proof steps with the explicit coefficient-quotient hypotheses checked in the completion comparison.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.
- `searches.jsonl` — retained search log from the earlier attempt; no new DAG node was created.

## Attachments

None. I searched the project source for the item id, its title and the relevant tensor/completion/Frobenius names; no sorry-free project declaration states this item exactly.

## WANTED:

None.

## What was wrong or incomplete in the earlier sandbox

The earlier sandbox had no report, so the delivery could not pass its required NF review section. Its second proof step also invoked the constant-completion comparison without spelling out the coefficient hypotheses (finite residue quotient, finite quotient rings, and perfect two-term resolutions); those checks are now included. I changed the fourth step from `elementary: true` to `false`, since it uses a naturality square and typed composition rather than a one-line definitional rearrangement. The statement is unchanged, and no source error or statement dispute was found.

## What I could not finish

Nothing. This is a stage-1 natural-language split only; no Lean file was written and no compiler or build tool was run.

## Review by NF

I read the item node, the fixed chapter `sec-six-functors`, unit `sk-rem-sf-pf-done`, and the current blueprint proof `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md`. The item realizes the blueprint sentence “Its equivariance for Weil complexes is the equivariance of the projection transformation in [lem-fix-weil-operations].” I also read the complete statements of every dependency named by the item and its proof, and checked the existing DAG for duplicate nodes before deciding that no auxiliary node was needed. The six off-unit dependencies listed in `split_report.tool_uses` are used only as generic coefficient-category, completion, or scalar-extension tools; none replaces a route step supplied by this unit.

Step 1 uses `lem-weil-pbc-integral-stratified-perfect-characterization` for the identification of the integral constructible category and its reduction functors, `def-wf-weil-category` for the coefficient conventions, and `lem-fix-constructible-tensor-completion` for derived completeness and the natural ordinary-to-completed comparison. I verified its hypotheses: the geometric fibre of a separated finite-type scheme over a finite field is quasi-compact, quasi-separated, noetherian and finite-dimensional, and multiplication by `ell` is invertible because `ell != p`.

Step 2 uses the explicit Koszul completion definition `def-weil-pbc-intrinsic-completion`, unit naturality from `lem-weil-pbc-ringed-koszul-completion-reflector`, and the final comparison clause of `lem-weil-pbc-constant-completion-equivalence`. It uses `lem-weil-l-adic-extension-integers-dvr` for the coefficient ring. I checked every coefficient hypothesis required by that comparison: the DVR gives a PID and hence a Noetherian ring, its residue field is finite, `R/(varpi)` is finite and additive-torsion, every `R/(varpi^n)` is finite, and multiplication by `varpi^n` gives a finite-free two-term resolution, so each quotient is perfect. The cited comparison explicitly identifies the Koszul and quotient-tower limits and their units, which is the identification used here.

Step 3 uses the completed-pullback and tensor chain models stated in `def-wf-weil-category`, `def-wf-tensor-product`, and `def-weil-pbc-intrinsic-completion`. I checked the actual strict mapping-fibre calculation: the Frobenius coefficient map fixes the residue of `varpi`, so it preserves the degree-zero inclusions into each Koszul factor and all tower transitions. The product comparison therefore carries the unit chain map to the target unit chain map, including the zero shifted component. This establishes the displayed equality of the ordinary and completed pullback-tensor comparisons at chain level rather than assuming equality merely from finite reductions.

Step 4 uses the tensor-map convention in `def-wf-tensor-product`, naturality of the completion unit in `lem-weil-pbc-ringed-koszul-completion-reflector`, and the Weil morphism equation in `def-wf-weil-category`. I checked the types of `v`, `C(v)`, the ordinary comparison, and the completed comparison. Substituting Step 3 into the naturality square gives exactly `chi varphi_T = varphi_hatT Phi_W^*(chi)`; multiplying by the inverse comparison gives the inverse Weil morphism. The step is marked non-elementary because this is a composed naturality argument.

Step 5 uses raw rationalization and tensor localization from `def-weil-pbc-rational-category` and `def-wf-tensor-product`, finite-free coefficient comparison from `lem-weil-finite-free-completed-scalar-comparison`, the natural tensor/scalar-extension and coherence maps from `lem-pur-integral-operations-scalar-extension`, and the common-stage representative rules from `def-wf-weil-category`. I checked that integral constructible inputs are derived-complete before applying the finite-free comparison, that numerator representatives may be chosen for localized morphisms and divided by a common power of `varpi`, and that finite freeness lets the finite direct-sum scalar extension commute with the product/mapping-fibre model. The quotient-map formula is the same at each finite stage and composes by `(x tensor s) tensor t` mapping to `x tensor (s t)`, so the equality is independent of the chosen common field. Small cases (zero inputs, identity Frobenius, empty fibre, and `E=L`) reduce to the identity comparison and agree with the proof.

Finally, I checked `citations.json` against the exact current statements: every proof-step citation has a verbatim quote, and `proof_deps` is the union of the step uses. The server-side `review_split` check passed before this report was written; the next dry run will perform the complete delivery preflight.
