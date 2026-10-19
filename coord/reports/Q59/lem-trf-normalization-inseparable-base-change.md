Files written:

- Item: \`dag/nodes/sec-trace-formula/lem-trf-normalization-inseparable-base-change.json\` (statement, split; no new node).
- Citations: \`citations.json\` with 19 verbatim statement quotes.
- No new nodes; consequently there are no Mathlib-leaf verdicts to report.

Attachments: none.

WANTED: none.

The imported item was unsplit and had creator metadata for Q90's parent item; I corrected the creator to Q59 and this item. I found no declaration tagged \`(blueprint: lem-trf-normalization-inseparable-base-change)\` in the read-only Lean source, so this is a genuine stage-1 split. The existing DAG already supplies the needed normalization and finite-normal comparison statements; creating another clause node would have duplicated the item.

## Review by Q59

I read the item, its chapter and unit records, the parent blueprint proof, and the Stacks sources named in the item (varieties Tags 0C3N, 038M and 038O, together with the purely inseparable homeomorphism and finite-normal comparison material). I also read the full statements of every cited node: \`lem-pc-homeo-pure-insep\`, \`lem-weil-pbc-reduced-algebraic-normalization-field-change\`, \`lem-sbc-finite-normal-dense-open-iso\`, \`lem-sbc-integral-closure-finite-normal-product\`, \`lem-sc-normalization-exists\`, \`lem-weil-pbc-finite-type-over-noetherian\`, and the definition nodes used by the four steps.

Step 1 checks that purely inseparable base change preserves the underlying irreducible space, that reduction is integral, and that the existing reduced-normalization statement supplies finite surjectivity and a dense normal-locus isomorphism. Normality of the integral-closure normalization is taken from the cited finite-product normality statement, rather than from the normalization definition.

Step 2 checks that geometric normality makes the base-changed \(N_1\) normal with domain stalks and that the homeomorphism identifies its underlying space with \(N_1\). The finite map descends through the reduction, and the dense normal locus pulls back to a dense open \(U_2\); the displayed isomorphism over \(U_2\) is the base change of the one supplied in Step 1.

Step 3 checks all hypotheses of the existing finite-normal dense-open comparison: \(X_2\) is locally Noetherian by finite type over a field, both source schemes have normal-domain stalks, both maps are finite, and the inverse images of \(U_2\) are dense. The resulting isomorphism is over \(X_2\), hence over \(C_{k_2}\). Its uniqueness follows because an automorphism over \(X_2\) is the identity on the dense normal locus and finite separated maps from reduced sources are determined there. Base changing this isomorphism to any \(L/k_2\) gives the geometric-normality clause.

Step 4 is the defining fibre-product calculation for a closed subscheme and reduction. Finiteness of a finite morphism survives base change and passage to a closed reduced subscheme, giving the final assertion. I checked the edge cases \(C=\varnothing\), \(k_1=k\), \(k_2=k_1\), and \(D_1=\varnothing\); each clause remains valid. The Mathlib searches were rerun with the item id using LeanFinder, Loogle, grep and LeanSearch; no exact Mathlib theorem states this scheme-level comparison.

