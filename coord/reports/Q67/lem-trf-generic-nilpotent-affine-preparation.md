## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-generic-nilpotent-affine-preparation.json`: split in seven steps; unchanged statement; Mathlib searches find ingredients only.
- `citations.json`: one verbatim statement quotation for every dependency of every proof step.
- `searches.jsonl`: actual msearch outputs, retained unmodified.
- `report.md`: this report.

## New nodes

None. Zero new Mathlib leaves. The proof reuses twenty existing nodes, including existing Mathlib leaves. The nilpotent denominator arithmetic is a proof step, not a new node restating the existential clause.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, nonreduced/nonReduced, and generic/nilpotent in both orders. The GenericTensorNilpotence files concern algebraic annihilator descent, not the whole geometric statement with reduction, all residue fields, and affine restriction compatibility. No exact completed project declaration was found.

## WANTED

None. All source arguments used are in the local Stacks files.

## Findings and route

The item was unsplit with no sandbox copy or earlier split/report. Its statement is correct and unchanged. Its source is Stacks 0575, `more-morphisms.tex`, `lemma-nonreduced-in-neighbourhood`, from reduction of the base through the two shrinkings, stopping before generic flatness. I read that whole proof. The item belongs to chapter `sec-trace-formula`, unit `sk-i-curve-zero`; I read both records, the three levels in SETUP, GOAL, and the newest blueprint locality proof in `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`. This is the existing commutative-algebra constructibility branch below that ancestor, not a replacement for the contracting-correspondence argument. No chapter, unit, target, or statement changed.

Whole-DAG searches covered reduction and residue fields, nilpotence and localization, finite type affine charts, and affine fibre products; I opened the candidate statements rather than taking their names as evidence. In particular `lem-trf-fibre-open-affine-reduction` requires flatness and geometrically reduced fibres and is unusable here; `lem-trf-lft-finite-relative-affine-atlas` imposes qcqs schemes; the generic-flat reduced-base model would unnecessarily introduce generic flatness. The suitable general existing nodes are cited instead. `tools/blueprint_refs.py ancestor` gives `lem-trf-local-term-locality`; blueprint searches for nilpotent, nonreduced, and reduction find no equivalent blueprint node. The item's existing precise `from.place` and `same_as=[]` are retained.

I ran all four msearch kinds and a second semantic phrasing, and read each result. The item retains its earlier search history and appends precisely the new logged queries. Properties.lean supplies reducedness/integrality and affine reducedness, Geometrically/Reduced.lean gives reduced fibres under geometric reducedness, and Spectrum/Prime/Polynomial.lean's nilpotence test assumes a finite free algebra. None gives the full preparation. No new node requires additional searches.

## Not duplicates

No new nodes, hence no same-tag pairs to distinguish. Existing nodes for 054M, 01T4, 01T2, 01JR, 01I4, 01HV, and 00DK are reused directly.

## Review by Q67

I checked delivery-errors B through E against the source and all twenty cited statements. Every proof step is below 2000 characters (the longest is 1128); none conceals a separate comparison lemma. The two localization comparisons in step 6 are the same explicit fraction construction and uniqueness argument as the cited universal property, not an uncited descent theorem.

Step 1 uses the complete reducedness and universal-homeomorphism statement of `lem-weil-pbc-reduction-universal-homeomorphism`, the closure definition of `def-sc-generic-point`, and the reduced/irreducible equivalence explicitly included in `def-pc-integral-scheme`. Clause (2) of `lem-sfb-finite-type-composition-base-change` really gives finite type after arbitrary base change, with no Noetherian hypothesis. I checked Stacks 054M (`lemma-reduction-universal-homeomorphism`), Schemes 01J3 (`lemma-reduced-closed-subscheme`), Properties 01ON (`lemma-characterize-integral`), and Morphisms 01T4 (`lemma-base-change-finite-type`). Irreducibility is transported by a homeomorphism, not asserted of a general base change.

Step 2 uses `lem-weil-pbc-closed-immersion-residue-field-iso` exactly for its field isomorphism, and the full cartesian square of `lem-weil-pbc-fibre-of-base-change`. The reduction is a closed immersion by step 1, so the hypothesis is available. The inverse comparison is constructed from the inverse field map using `def-pc-fibre-product`; one does not infer a scheme isomorphism from a bijection of points. The off-unit residue-field lemma is declared in `split_report.tool_uses` as a generic scheme tool. No replacement in this unit states it. This verifies the first paragraph of 0575 rather than silently using its assertion.

Step 3 uses `lem-weil-pbc-affine-opens-basis` to choose a neighbourhood of the generic point, then `def-pc-integral-scheme` for the domain ring. `lem-weil-pbc-spec-domain-stalks-function-field` explicitly identifies the generic prime (0) and its stalk with the fraction field; `def-weil-residue-field` then identifies its residue field. Restriction of the family uses the actual base-change clause already cited and fibre-product uniqueness, so no extra condition on T or X is introduced.

Step 4 starts at a nonreduced stalk, as permitted by `def-pc-reduced-scheme`, and uses the affine basis at its image in the total scheme, not an unjustified lift of an arbitrary open of the fibre. `lem-weil-pbc-lft-affine-pairs` supplies finite type for this chosen chart. `lem-weil-pbc-affine-chart-base-change-iso` gives the entire inverse-image affine chart, with its map on coordinates, for an arbitrary scheme over an affine base. `lem-weil-pbc-affine-open-stalk-localization` gives the local ring of this chart at the chosen point, and `lem-weil-pbc-localization-preserves-reduced` applies to that prime localization if its coordinate ring were reduced. This contradiction provides the nonzero nilpotent. I read Schemes 01JR (`lemma-open-fibre-product`), 01I4 (`lemma-fibre-product-affine-schemes`), 01HV (`lemma-spec-sheaves`), the definition and affine criterion in the reduced-schemes section, and Morphisms 01T2 (`lemma-locally-finite-type-characterize`). Tensor symmetry is written on pure tensors, with inverse, rather than hidden in the word transport.

Step 5 uses the full localization statement, including fraction representation and zero criterion, of `lem-weil-pbc-localization-base-change`. It only assumes a domain for A0, never for B0. The annihilating scalar u and denominator s are nonzero in A0, so their product g is nonzero there, even if the map A0 to B0 has torsion. `lem-weil-pbc-affine-open-section-vanishing-prime` states an affine open and a ring localization, stronger than the purely topological basic-open node (which would not suffice). The two cited geometric fibre-product statements give the open immersion and the affine ring with projections. I read Schemes 01I3 (`lemma-standard-open-affine`), 01HV, 01JR, 01I4 and Algebra 00DK (`lemma-tensor-localization`).

Step 6 is elementary fraction arithmetic after the preceding cited facts. I checked s inverse = u/g, u inverse = s/g, and b=c/s, so u c^n=0 really implies b^n=0. The two maps between fraction fields and the two maps between generic chart rings are determined on numerators and denominator inverses by `lem-weil-pbc-ring-localization-universal-property`; `lem-weil-pbc-localization-base-change` supplies that the tensor rings are precisely those localizations. This verifies that the resulting b has the original generic image h, rather than just some nilpotent image. Finite algebra generators remain generators after localizing coefficients, as the displayed polynomial/fraction formula proves. No generic freeness, no flatness, and no injection of B0 into its generic fibre are used.

Step 7 uses `lem-weil-pbc-affine-open-section-vanishing-prime` for the scheme D(a), `lem-weil-pbc-open-fibre-product` for its inverse-image open, `lem-weil-pbc-fibre-product-affine-spectra` for its affine tensor ring and both projections, and `lem-weil-pbc-localization-base-change` for that ring's canonical identification with B_a. Each cited statement contains exactly these conclusions. This is not inferred from the topological homeomorphism Spec A_a onto D(a).

Small cases checked: a=0 gives the empty source and target principal opens and zero localization rings; a=1 gives the original chart. If T is already integral the reduction comparison is the identity. A field base has no shrinking obstruction (all nonzero scalars are units); dual numbers over that field give b=epsilon. A nonreduced base is allowed throughout the first two steps, with no assumption that its nilradical is finitely generated or nilpotent. The zero scheme and reduced generic fibres cannot meet the nonreduced-generic-fibre hypothesis. The nilpotence exponent is positive; exponent zero would force h=0. General torsion in B0 is allowed and is exactly why the second shrinking uses u.

No statement correction, source error, or outstanding mathematical issue was found. Corrections made while drafting were to cite the scheme-level principal-open lemma instead of its topological counterpart, and to use the general affine-chart pullback statement instead of special fibre lemmas with flatness or finite-presentation hypotheses. Citation quotations are literal full statements, making every available clause reviewable. No Lean or compiler tools were used.

## Unfinished

None for this one-level split. Independent maintainer review follows delivery.
