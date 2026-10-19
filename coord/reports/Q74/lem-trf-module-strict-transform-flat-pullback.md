# Worker report: lem-trf-module-strict-transform-flat-pullback

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-module-strict-transform-flat-pullback.json`: split into four proof steps; no statement change; two Mathlib leaves cited.
- `dag/nodes/sec-trace-formula/lem-trf-flat-pullback-exact.json`: Mathlib leaf `Module.Flat.lTensor_exact`.
- `dag/nodes/sec-trace-formula/lem-trf-flat-morphism-base-change.json`: Mathlib leaf `AlgebraicGeometry.Flat.isStableUnderBaseChange`.
- `citations.json`: verbatim statement quotations for every step citation.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration carrying the blueprint tag or stating the item without `sorry`.

## WANTED:

None.

## Corrections and scope

The imported node was unsplit and had the correct hypotheses and conclusion. I retained the finite-type quasi-coherent centre, the specified flat blowup comparison, and the requirement that the induced quotient isomorphism commute with the ordinary quotient maps. I added the two genuinely external ingredients needed by the proof: flatness of a scheme morphism after base change and exactness of tensoring by a flat module. The remaining kernel comparison is done sectionwise from the supported-section description in the existing sheaf-kernel node; no separate duplicate node was created.

## Not duplicates

lem-trf-module-strict-transform-flat-pullback vs lem-trf-strict-transform-sheaf-kernel: the existing node describes the supported kernel and quasi-coherence for one strict transform; this item compares kernels after a flat source/base pullback.

lem-trf-module-strict-transform-flat-pullback vs def-trf-module-strict-transform: the existing node defines the quotient by supported sections; this item proves its canonical compatibility with flat pullback.

lem-trf-module-strict-transform-flat-pullback vs lem-trf-module-admissible-blowup-calculus: that node concerns successive admissible blowups and preservation of flat modules, while this item compares a single strict transform with an independently flat source and base change.

## Review by Q74

I read the item, the ancestor blueprint proof, the Stacks Project passages for Tag 080D (module strict transform), Tag 0805 (flat base change of blowups), Tag 0814 (the local pullback compatibility used in flattening), and the existing nodes `def-trf-module-strict-transform`, `lem-trf-strict-transform-sheaf-kernel`, `def-pc-fibre-product`, and `def-pc-module-pullback`. Step 1 uses the exact statement of the blowup comparison theorem to identify the base-changed blowup and checks that the fibre-product square defining (j^b) is the base-change square. Step 2 uses the definition and the existing kernel lemma to identify each strict transform as a quotient by the supported-section kernel. Step 3 verifies the hypothesis that the induced map is flat by the Mathlib base-change leaf and uses the Mathlib tensor-exactness leaf on affine charts; the complement of the exceptional divisor pulls back to the corresponding complement, so the two supported kernels agree sectionwise. Step 4 applies the cokernel universal property and the canonical pullback composition map, and I checked that its composite with each quotient map is the prescribed one. I tested the unit-ideal, zero-module, identity-source, and identity-base cases; all reduce to the ordinary pullback quotient. The two Mathlib searches for each new leaf were run with `msearch.py`, and every recorded query is present in `searches.jsonl`.
