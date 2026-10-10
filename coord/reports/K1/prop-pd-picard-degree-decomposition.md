# Stage 1 report

1. Files written:

- `dag/nodes/sec-picard-framework/prop-pd-picard-degree-decomposition.json` (statement; split; no Mathlib match).
- `dag/nodes/sec-picard-framework/rem-pc-group-structure.json` (statement-only group-structure tool node; no Mathlib match).
- `citations.json`.

2. Attachments:

- `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H` belongs to `lem-pc-cohomology-sections-affine-base`.

3. WANTED:

None.

4. What was wrong or incomplete:

The imported item was marked as resting on sorry despite having a body in slopmaster2; its declaration is therefore not attachable. Its proof had an uncited use of the integral nonzero-section Cartier argument and an unclassified subgroup step. I cited the existing `lem-pc-nonzero-section-integral-cartier`, marked subgroup closure elementary, declared the three off-unit tool uses required by the route review, and added the missing group-structure statement node referenced by the item. The source blueprint's single paragraph is realized by six checkable proof steps.

5. What could not be finished:

No proof obligations remain in this split; the new group-structure node is intentionally statement-only for the next stage.

## Review by K1

I read the item source `literature/blueprint/master/blueprint/sec-picard-framework/sk-prop-picard-degree-decomposition/prop-pd-picard-degree-decomposition.md`, the unit record, and `WeilConjectures/AlgebraicGeometry/Picard/Jacobian.lean` lines 441-566. The Lean theorem has the expected decomposition statement but is transitively open, so I did not attach it. I also read the source declarations in `Picard/Degree.lean`, `Cohomology/DirectImage.lean` lines 307-324 and 574-615, and the existing DAG statements used by every proof step.

Step 1 uses the existing base-change integrality proposition, fibrewise-degree definition, degree-morphism definition, and local-constancy lemma; their statements supply exactly the geometric setup and compatibility claimed. Step 2 uses the degree definition, degree base-change/tensor statement, degree agreement for effective divisors, vanishing above dimension one, Euler characteristic definition, and the existing nonzero-section Cartier lemma; I checked the smooth projective integral hypotheses after field extension and the positive twist. Step 3 uses the degree morphism and local-constancy statement; the fppf-local tensor-product argument is written out. Step 4 uses the normalized universal-class isomorphism, degree morphism, and local constancy. Step 5 is marked elementary because it restricts the preceding additivity and inverse identities to the degree-zero open. Step 6 uses the rational-point divisor degree clause of `lem-pc-degree-base-change` to identify translation by `O_C(dP)` and its inverse. The off-unit uses are declared in `split_report.tool_uses` and checked against their node statements. The new `rem-pc-group-structure` statement cites `def-pc-picard-functor` and is used only to supply the group-scheme clause in the item statement.

I tested the fieldwise argument on $C=\\mathbf P^1_k$ with $\\mathcal O(n)$, where the asserted degree additivity and translations give the usual integer degree, and on $d=0$ where translation is the identity. The Mathlib searches for the item and new node were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. No duplicate blueprint node or existing DAG node was found for the finite-free-complex statement.

## Second reading by K1

- Item statement: checked against the blueprint proposition and unit record; the field, curve, rational point, degree morphism, fibrewise-degree subfunctors, clopen decomposition, subgroup, and translation clauses agree hypothesis by hypothesis.
- Step 1: checked against `prop-pc-xk-integral`, `def-pd-fibrewise-degree`, `def-pd-degree-morphism`, and `lem-pd-degree-locally-constant`; the field-extension and geometric-integrality hypotheses are present and the local-constancy conclusion is exactly used.
- Step 2: checked against the degree, effective-divisor, vanishing, Euler-characteristic, and nonzero-section Cartier nodes; the twist choice, nonzero section, Cartier zero divisor, and cancellation of the added point-divisor degree are valid, including negative degrees after cancellation.
- Step 3: checked against the degree-morphism and local-constancy nodes; the fppf-local representatives, tensor product, residue-field fibre calculation, and subgroup consequences are stated explicitly.
- Step 4: checked against `cor-pc-sigma-pic-iso`, `def-pd-degree-morphism`, and `lem-pd-degree-locally-constant`; the normalized universal class yields the invertible module and factorization through the open pieces.
- Step 5: checked as an elementary consequence of Steps 3 and 4; unit, multiplication, and inverse preserve degree zero, so no additional node is needed.
- Step 6: checked against the rational-point clause of `lem-pc-degree-base-change` and Step 2; translation by the degree-​d divisor and its inverse are mutually inverse and restrict to the claimed pieces.
- New node `rem-pc-group-structure`: checked as self-contained against `def-pc-picard-functor` and the group-valued Picard construction in `Picard/Group.lean`; it supplies the group-scheme structure used in the item statement and is not a restatement of a numbered conclusion.
- New node `prop-pd-picard-degree-decomposition`: checked for statement-only form, definition dependencies, TeX, blueprint metadata, and recorded Mathlib searches; it is the split item and has the complete six-step proof separately.
- Small cases checked: $d=0$ gives the identity translation and degree-zero subgroup; $C=\\mathbf P^1_k$ gives the usual integer degree for $\\mathcal O(n)$; field extension preserves fibre degrees; the empty test scheme makes the fibrewise condition vacuous.
- Changes made: none. The independent reading found no mathematical or contract defect; the dry-run preflight passed.
