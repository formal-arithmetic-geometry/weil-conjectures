# Stage-1 report: lem-fd-affine-space-thom-coefficient-transport

## Files written

- `dag/nodes/sec-fourier-transform/lem-fd-affine-space-thom-coefficient-transport.json`: split statement, no new nodes.
- `citations.json`: verbatim citations for all five proof steps.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the item id, its title, and the relevant Thom/integration declarations; no sorry-free project declaration states this item exactly.

## WANTED

None. The cited blueprint and DAG statements are available locally.

## What I checked and changed

The imported item was statement-only and had already recorded Mathlib searches. I retained its statement and coefficient conventions, added the existing affine-space smoothness statement to `stmt_deps`, and expanded the proof into five steps. I searched the whole DAG and blueprint for duplicate coefficient-transport or affine-space Thom nodes; the existing `thm-pur-vector-bundle-thom`, finite reduction, adic trace, scalar transport, and coefficient-comparison nodes provide the needed ingredients, so no new node was created.

## Review by Q118

I read the item source in `literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-prop-convolution-kernel/lem-fd-convolution-kernel.proof.md`, including both paragraphs that invoke the compact-support Thom computation, and the coefficient-transport source `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sp-trace/sk-def-sp-trace-properties.proof.md`, clause (2). I also read the statements of every node cited by the five steps.

Step 1 uses `sbc-lem-affine-space-smooth` for the smooth pure relative dimension of the affine projection, `thm-pur-vector-bundle-thom` for invertibility of the trivial vector-bundle Thom map, and `det-sp-trace-basic` for its identification with normalized affine integration and the origin class. I checked that the base is separated finite type, that the trivial bundle has rank `m`, and that the `m=0` case is the identity.

Step 2 uses the explicit derived-limit construction in `def-weil-integral-rational-qbar-compact-support`, the coherent finite-level lift in `thm-pur-adic-reconstruction`, its trace-coherence proposition, and the reduction compatibility in `thm-pur-finite-reduction-of-purity`. The cited `lem-weil-derived-limit-levelwise-iso` states that a tower map with levelwise isomorphisms induces an isomorphism on derived limits. I verified that each finite reduction is exactly the normalized map from Step 1 and that the origin normalization is preserved.

Step 3 uses `thm-pur-rational-and-qbar-purity` and `prop-pur-rational-purity-trace-coherence` to identify the rational and common-stage traces with transported integral traces, `prop-weil-pbc-rational-transport` for localization of natural transformations, and `def-weil-algebraically-closed-coefficients` for finite-stage representatives. I checked that the argument proves isomorphy after scalar transport and does not introduce a new coefficient hypothesis.

Step 4 uses `lem-pur-adic-scalar-trace-coherence` for the explicit finite-extension trace equation, `lem-pur-compact-support-integral-coefficient-comparison` for its reduction and compact-support comparison, `lem-pur-finite-universal-smooth-trace` for finite-free normalization, and `prop-weil-pbc-scalar-extension` for associativity and units. I checked that the source and target of each displayed comparison match the item’s $t_{m,\Lambda}$ maps, including ramified extensions.

Step 5 is the elementary inverse twist and shift reformulation from the source: tensoring by the inverse Tate twist and inverse shift turns the normalized map into `Rπ_! Λ ≅ Λ(-m)[-2m]`; at rank zero all comparisons are units. I corrected the only mechanical issue found by the server check, replacing a nonexistent dependency name with the existing `prop-weil-pbc-rational-transport` node. The sandbox then passed `srvcheck.py ... check_dag`.

## Not duplicates

No new nodes were created, so there are no new duplicate pairs.
