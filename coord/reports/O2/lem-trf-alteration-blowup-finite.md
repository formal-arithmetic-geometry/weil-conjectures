# Stage-1 report: lem-trf-alteration-blowup-finite

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-alteration-blowup-finite.json`: repaired four-step statement split.
- `citations.json`: verbatim statements for every node used by every step.
- `report.md`: this worker report and repair review.

Attachments: none.

WANTED: `literature/orgogozo-modifications-cycles-proches.pdf`, Lemma 2.5 p. 4 and the proof of Lemma 3.2.1 p. 8, for `lem-trf-alteration-blowup-finite`; the local archival PDF is absent. The proof origin remains agent-written and follows the Stacks flattening and strict-transform route.

## Not duplicates

`lem-trf-alteration-blowup-finite` vs `lem-trf-alteration-finite-refinement`: the existing node asserts arbitrary modifications and a finite surjective refinement, while this item specifies a nowhere-dense blowup center, the strict-transform blowup of the source, and the resulting blowup diagram.

## What was repaired

The returned version had malformed single-backslash `\\times`/`\\to` escapes in the JSON step text, used `flat.tex` as the source for Tags 052A and 051T, omitted `lem-trf-finite-after-blowup` from step 1's uses, used the wrong scheme-theoretic-density lemma in step 3, omitted properness of the target blowup in step 4, and treated the open in the source blowup as `U` rather than `a^{-1}(U)`. It also left the generic-flatness lemma undeclared as an off-unit tool. These are all corrected. Step 2 now cites `lemma-nagata-admissible-blowup-over-open`; step 3 uses `lemma-nagata-conrad-dense-in-admissible-blowup` for the required topological density; and step 4 cites `lemma-nagata-blowup-proper`, applies the over-open and Conrad lemmas to `Z` and to `W` with the extended ideal, and explicitly proves density of `a^{-1}(U)` in the integral source.

## Review by N2

I reread the item statement, the unit `sk-i-curve-zero`, the parent blueprint sentence invoking Orgogozo Lemma 2.5, and the Stacks sources used by each step. The item statement is unchanged. For step 1 I checked the alteration clauses and properness in `morphisms.tex` Tag 01W1, generic flatness in `morphisms.tex` Tag 052A together with the finite-presentation clause in `algebra.tex` Tag 051T, and the finite-after-blowup node at `flat.tex` Tag 0B49. The source metadata now names the correct documents. The step's hypotheses give a nonempty affine finite-flat-locally-presented locus, and it explicitly uses `lem-trf-finite-after-blowup`.

For step 2 I read the statements of `lem-trf-finite-after-blowup`, `def-nagata-admissible-blowup`, `lemma-nagata-admissible-blowup-over-open`, `def-weil-closed-immersion`, `lemma-nagata-strict-transform-over-complement`, and the alteration definition. The admissible ideal is the unit ideal on `U`, the target blowup is identified over `U`, its closed center is disjoint from the dense open, and the strict transform agrees with the finite alteration over that open.

For step 3 I read the finite-locally-free, finite-proper, proper, finite-integral, and `lemma-nagata-conrad-dense-in-admissible-blowup` statements. The image of the finite map is closed, contains `v^{-1}(U)`, and the Conrad lemma supplies the topological density actually required; no scheme-theoretic-density hypothesis is silently assumed.

For step 4 I read `def-nagata-strict-transform`, `lemma-nagata-blowup-proper`, proper base change, properness of closed immersions, `lemma-nagata-admissible-blowup-over-open`, `thm-nagata-strict-transform-is-blowup`, and the Conrad density lemma. The open preserved on the source is explicitly `U_W=a^{-1}(U)`. Surjectivity of the alteration makes this a nonempty open of integral `W`, hence dense, and finiteness over affine `U` makes it quasi-compact. The source blowup uses the extended ideal, so the over-open and Conrad statements apply to `W` and prove that `u^{-1}(U_W)` is dense. Properness of `v` is now cited before proper base change, and the strict-transform blowup theorem supplies the compatibility `a∘u=v∘p`.

I checked the empty-center case (both blowups are identities), a nontrivial finite alteration such as `t↦t^2`, and the blowup of `\mathbb A^2` at a point. The corrected JSON escapes parse as intended, every citation quote is verbatim, `proof_deps` is the union of step uses, and the only off-unit split node (`lem-sbc-generic-flat-finite-presentation`) is declared in `split_report.tool_uses`. No SGA source is used and no new node was created.
