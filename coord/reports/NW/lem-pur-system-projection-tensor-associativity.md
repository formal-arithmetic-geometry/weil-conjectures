# Stage-1 worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-system-projection-tensor-associativity.json`: item, split with six proof steps; no new nodes.
- `citations.json`: verbatim statement fragments for every node used by every proof step.
- `searches.jsonl`: inherited searches plus the three fresh msearch.py queries run for the item.
- `report.md`: this report and the NW review.

## Attachments

None. I searched the slopmaster2 source by the item id, projection/tensor terminology, and likely declaration names; no sorry-free project declaration states the item exactly. The existing strict-system projection-coherence node was reused as a dependency.

## Literature wanted

None. The proof follows the agent-formulated tensor calculation in the current blueprint proof paragraph and the counit projection construction at Stacks Tag 0B56; no additional document was needed.

## Corrections and limitations

No STATEMENT-DISPUTED: the statement is well typed and retains the strict-system, finite-type, coefficient, and no-common-bound hypotheses. No new node was created. The imported Mathlib searches were read and reused; fresh searches found only generic tensor/mate declarations and no exact compact-support strict-system theorem.

## Review by NW

I read the item node, its unit `sk-thm-purity-transport`, chapter `sec-smooth-purity`, and the current blueprint paragraph named in the node. I also read the full statements of `def-exchange-projection`, `lem-pur-system-level-projection-formula-coherence`, `lem-coef-finite-adjunction-diagram-realization`, and `lem-coef-semilinear-derived-sections`. Step 1 uses the definition's counit-defined proper projection followed by the open tensor comparison, and the two realization nodes explicitly provide the same strict-system models and finite compact-support functors. The coherence node confirms that the projection maps are the specified maps and are natural in both inputs.

For Step 2 I checked the cited ringed-topos mate statement: its projection transformation is adjoint to `(ε_E ⊗ 1) μ`, with μ the natural pullback-tensor comparison. I expanded both proper mates and verified that they use the same two μ maps, counit, and tensor associator, so no invertibility is used. The cited pullback-tensor node supplies the natural comparison. Step 3 uses the exact open-immersion projection formula; applying it twice gives the same extension-by-zero comparison, with the pullback-tensor node providing the canonical h-pullback reassociation. Step 4 combines those two calculations through the exact compactification definition and checks equality before any total inverse limit in the simultaneous section models.

For Step 5 I checked the hypotheses carefully: naturality in the first tensor input transports the assumed invertibility for `h^*L' ⊗ M` to `M ⊗ h^*L'`; the first identity then gives invertibility for `L' ⊗ L`, and naturality in the second input plus the symmetry gives `L ⊗ L'`. Step 6 expands the stated Q maps, substitutes the inverse projection identity, and cancels only canonical symmetry and associator isomorphisms. The result has the exact source and target in the item. I tested identity morphisms, the empty scheme, zero systems, and `L=1` on the formulas; all reduce to the corresponding unit or zero identities. No proof step exceeds 2000 characters, no SGA source is cited, and the duplicate search found no other node stating this tensor-variable identity.
