# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-pure-relative-dimension-finite-stage.json` — split item.
- `dag/nodes/sec-trace-formula/lem-trf-limit-fibre-dimension-bound.json` — new unsplit statement node (no Mathlib match).
- `dag/nodes/sec-trace-formula/lem-trf-relative-dimension-base-change.json` — new unsplit statement node (no Mathlib match).
- `dag/nodes/sec-trace-formula/lem-trf-retrocompact-bounded-fibre-dimension.json` — new unsplit statement node (no Mathlib match).

## Attachments

None.

## WANTED

None.

## Not duplicates

- `lem-trf-limit-fibre-dimension-bound` vs `lem-weil-pbc-affine-limit-fibre-dimension-bound`: the new node is the general scheme statement of Tag 05M5; the existing node is only an affine ring-system specialization with explicit tensor-product hypotheses.
- `lem-trf-retrocompact-bounded-fibre-dimension` vs `lem-weil-pbc-local-fibre-dimension-open`: the new node includes retrocompactness under locally finite presentation (Tag 02G0); the existing node states openness only for locally finite type (Tag 02FZ).
- `lem-trf-relative-dimension-base-change` vs `lem-sc-curve-base-change-relative-dimension-one`: the new node is arbitrary pure dimension d and arbitrary base change; the existing node is restricted to smooth curves of relative dimension one over a field.

## Source and statement checks

The item statement was checked against Stacks Limits Tag 0EY2 (lemma-descend-dimension-d) in `limits.tex`, together with Morphisms Tags 02NJ, 02NK and 02FY. I also read the exact definitions and the existing DAG statements for scheme limits, affine transitions, fibre products, scheme-theoretic fibres, pure dimension, local fibre dimension, constructible subsets, and qcqs permanence. The statement keeps the nonempty-fibre convention and does not add flatness, separatedness, or properness.

The proof follows the source. Step 1 constructs the base-change systems and verifies finite type and closed-immersion transition maps using the existing scheme-over-limit and qcqs/base-change statements. Step 2 applies the new general Tag 05M5 statement to descend the upper bound. Step 3 applies the new Tag 02G0 statement and forms the constructible complement. Step 4 checks pointwise containment of the limit image in that complement using the existing Tag 02FY local-dimension comparison and purity definition. Step 5 applies the existing constructible-containment node (Tag 05F4) to obtain eventual containment at finite stages. Step 6 compares local dimensions twice by Tag 02FY, combines the lower and upper bounds, and unfolds pure dimension componentwise.

I checked hypotheses at each use: all stage bases are qcqs with affine transitions; the base-changed morphisms remain locally finitely presented and finite type; the limit fibres satisfy the assumed pure dimension; and the constructible set is taken in the stage-0 source. Empty fibres are vacuous, and d=0 reduces the inequalities to local dimension zero. The Mathlib search log records LeanSearch, Loogle, LeanFinder, and Mathlib grep for each of the three new nodes; no theorem matched the general Stacks statements. The existing affine bound, local openness, scheme-over-limit, constructible-containment, fibre-dimension base-change, and qcqs nodes were read before citation.

## Review by Q66

I re-read all six item proof steps and every cited node statement. Step 1 uses only the scheme-over-limit construction, base-change permanence, and the new finite-stage bound; their statements explicitly provide the systems, finite-presentation stability, and closed-immersion hypothesis. Step 2 uses the new bound and the pure-dimension definition exactly for the implication “pure d implies dimension at most d.” Step 3 uses the new retrocompact-locus statement and the constructible-subset notion; its hypotheses are the item’s locally finite presentation and qcqs source. Step 4 uses the existing local fibre-dimension-after-base-change statement, the fibre and pure-dimension definitions, and checks the contradiction pointwise. Step 5 uses the existing constructible-containment statement and the scheme-over-limit statement; its E is constructible and the system has affine transitions. Step 6 uses the local-dimension equality under base change twice, then the pure-dimension definition; the two inequalities force local dimension d at every point, so each nonempty fibre component has dimension d. I corrected the imported empty proof by adding these explicit steps, adding the three genuinely missing general statements, and recording exact citations in `citations.json`.
- `lem-trf-relative-dimension-base-change` vs `lem-trf-pure-relative-dimension-finite-stage`: the new node is the general base-change lemma used as a proof input; the item additionally proves eventual descent through an inverse system.
- `lem-trf-relative-dimension-base-change` vs `lem-sc-fibre-dimension-after-base-change`: the new node concludes preservation of pure dimension for all components and all base changes; the existing node states pointwise fibre identification and equality of local dimensions.
- `lem-trf-relative-dimension-base-change` vs `lem-zl-affine-geometric-components-finite-extension`: the new node is a general scheme morphism statement; the existing node concerns affine geometric components after a field extension.
- `lem-trf-relative-dimension-base-change` vs `lem-sbc-smooth-relative-dimension-permanence`: the new node applies to arbitrary locally finite type morphisms with pure-dimensional fibres; the existing node assumes smoothness and relative dimension one.
- `lem-trf-relative-dimension-base-change` vs `lem-trf-flat-dense-generic-fibre-pure-dimension`: the new node is arbitrary base change of an already pure-dimensional family; the existing node derives purity from flatness and a dense generic fibre.
