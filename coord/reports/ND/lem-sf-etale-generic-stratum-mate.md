1. Files written:

- `dag/nodes/sec-six-functors/lem-sf-etale-generic-stratum-mate.json`: repaired the returned four-step proof; no new nodes and no Mathlib leaves.
- `citations.json`: 21 verbatim statement quotes for every cited node in every proof step.
- `report.md`: this repair report.

2. Attachments: none.

3. WANTED: none.

4. Repair of the returned delivery:

- Step 1 no longer cites `lem-amb-etale-adjoint-locality`. I checked `prop-weil-pbc-inverse-image-modules-exact` for the underived constant-coefficient module adjunction and exact inverse image, `lem-sc-derived-adjunction-from-underived` for passing to derived adjunctions, `lem-weil-pbc-extension-by-zero-adjunction` and `lem-weil-pbc-extension-by-zero-exact` for the open extension-by-zero adjunction and its exactness, and `lem-exc-closed-ambient` for the closed factor's ambient right adjoint. The step now derives both `s^* \\dashv Rs_*` and `Rs_! \\dashv Rs^!` in the stated ordinary categories and then composes the latter pair.
- Step 2 no longer takes theta from `lem-weil-stratum-ambient-hom`. I read `lem-sf-ringed-derived-closed-symmetric-monoidal` (which applies to any small ringed site and explicitly supplies the tensor-Hom bijection and evaluation), the immersion projection statement, and the two adjunction statements. It now constructs the natural Hom bijection from the tensor/projection/exceptional-adjunction chain.
- Step 3 applies Yoneda to that natural bijection to define the unique isomorphism theta. Thus theta is the specified map itself, rather than an unspecified ambient isomorphism whose normalization would need a separate comparison.
- Step 4 traces the inverse Yoneda bijection for an arbitrary `u:C\\to Rs_*H`. I used the evaluation-counit clause of the ringed-site node and wrote the four arrows through the projection, `Rs_!`, evaluation, and the exceptional counit. The step is marked non-elementary and cites every adjunction and projection it uses.

The only off-unit generic input is declared in `split_report.tool_uses`: `prop-weil-pbc-inverse-image-modules-exact` is used solely for the underived inverse-image/direct-image module adjunction and exactness, which the biduality route does not restate.

## Review by ND

I reread the returned item, its unit `sk-prop-sf-biduality-general`, the ancestor `thm-weil-etale-geometric-biduality`, and all seven cited statements used by the repair. I checked the coefficient ring is the same finite constant ring A throughout, that the open factor is exactly the given open immersion, and that the closed factor is the given closed immersion. The exactness hypotheses in the inverse-image module statement justify termwise derived inverse image, while the exact extension-by-zero statement justifies its derived open left adjoint. The generic derived-adjunction statement is used only to pass those underived adjunctions to the ordinary unbounded derived categories; the closed right adjoint is taken from the existing ambient statement. I checked the direction of every Hom bijection: tensor-Hom first, then the projection isomorphism, then `Rs_! \\dashv Rs^!`, then the tensor-Hom bijection on S, and finally `s^* \\dashv Rs_*`. This gives a bijection natural in the test object C, so Yoneda defines theta and proves it is an isomorphism. Finally I checked that the evaluation clause in the ringed-site statement gives exactly `Rs_!\\mathrm{ev}` and that the last arrow is the counit `\\varepsilon^!`; the displayed composite therefore matches the characterization in the item. I removed the prior unspecified ambient comparison and the invalid elementary normalization claim, and verified every entry in `citations.json` is a literal substring of the cited node statement.
