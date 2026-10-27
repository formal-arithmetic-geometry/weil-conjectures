# Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-rational-tensor-associator-scalar-square.json` — repaired item, split; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-integral-scalar-reduction-intertwining.json` — repaired statement-only scalarReduction interface, quantified over every normalized primitive scalar model; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-system-scalar-associator-coherence.json` — repaired statement-only associator interface for the fixed K-flat-normalized system calculus; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-integral-tensor-associator-naturality.json` — retained statement-only integral naturality interface.
- `citations.json` — verbatim quotations for every proof-step citation.
- `report.md` — this report.

Attachments:

- None. The rational and common-stage naturality declarations were inspected but cannot be cited because their dependency paths reach this item. The independent integral naturality interface is used instead.

WANTED: none.

The returned version left the stage3 limit-square uninstantiated, did not identify its tensor reduction with the fixed `r`, quantified gamma without the scalar model on which scalarReduction depends, and allowed an arbitrary system associator. I repaired these points. Step 1 now chooses the normalized primitive scalar and Roos data from the ambient comparison-system and primitive-scalar existence nodes, takes the tensor models from `stage3-pur-scalar-tensor-model-normalization`, and instantiates the existing stage3 limit-square. The gamma node is quantified over every normalized primitive scalar model and gives the explicit same-index quotient counit relative to `lem-pur-coefficient-extension-reduction-model`. The system node uses the fixed coefficient-system evaluation calculus and the K-flat-normalized closed symmetric tensor construction from `lem-coef-derived-system-evaluation-calculus` and `lem-sf-ringed-derived-closed-symmetric-monoidal`, so its associator is pinned without introducing the cycle through the higher wrapper node.

## Not duplicates

- `lem-pur-integral-scalar-reduction-intertwining` vs `lem-pur-coefficient-extension-reduction-model`: the existing node constructs the coherent reduction isomorphism for a completed scalar extension; the new node quantifies it over normalized primitive scalar models, names it `scalarReduction`, and spells out the same-index component used by the item.
- `lem-pur-integral-scalar-reduction-intertwining` vs `def-pur-scalar-extension-tower-data`: the existing definition records scalarReduction among tower data; the new node asserts its invertibility and its identification with gamma for each normalized scalar model.
- `lem-pur-integral-scalar-reduction-intertwining` vs `lem-trf-primitive-quotient-scalar-model-existence`: the existing node supplies the primitive-model construction context; the new node is the reduction comparison and its quotient formula, not model existence.
- `lem-pur-system-scalar-associator-coherence` vs `lem-sf-ringed-derived-closed-symmetric-monoidal`: the existing node supplies the K-flat-normalized closed symmetric tensor structure; the new node applies its pinned associator to derivedSigma scalar extensions and states the associator equation.
- `lem-pur-system-scalar-associator-coherence` vs `stage3-pur-derived-scalar-tensor-normalization`: the existing node gives derivedSigma existence and normalization; the new node states coherence of its two nested composites with the pinned systemClosed.monoidal associator.
- `lem-pur-rational-tensor-associator-scalar-square` vs `stage3-pur-scalar-tensor-model-normalization`: the existing stage3 node constructs a normalized tensor realization for one calculus and Roos model; the item additionally relates those models to the fixed integral associator, proves its scalar square, and localizes it rationally.
- `lem-pur-rational-tensor-associator-scalar-square` vs `stage3-pur-scalar-tensor-limit-square`: the existing stage3 node is the arbitrary-model completed limit square; the item instantiates it with the fixed models and adds fully-faithful reflection, rational localization, naturality, and pure-tensor extension.
- `lem-pur-rational-tensor-associator-scalar-square` vs `lem-pur-scalar-extension-tower-coherence`: the existing node proves strict quotient-tower scalar/pullback/tensor coherence and identifies derived limits; the item uses that identification to cancel gamma and the tensor reduction comparison in the associator square.
- `lem-pur-integral-tensor-associator-naturality` vs `lem-pur-rational-pullback-tensor-associator-natural`: the rational node follows the parent common-associator route; this independent integral equation is used before localization.
- `lem-pur-integral-tensor-associator-naturality` vs `lem-pur-cochain-pullback-tensor-coherence`: the cochain node is a chain-level comparison; this node states naturality of the completed derived associator.

## Review by NB

I reread the live item, the latest returned review, the current blueprint and unit records, the Lean sources for `DerivedPullbackTensorConstraints`, `ScalarExtensionTowerRealizationData`, `ScalarExtensionTensorModelNormalization`, and `IntegralOperationsScalarComparisons`, and every cited DAG statement.

For Step 1, I checked the hypotheses and roles of `lem-trf-ambient-comparison-system-existence` and `lem-trf-primitive-quotient-scalar-model-existence`. The former supplies the family of normalized Roos and scalar realization models; the latter supplies the primitive scalar-model context. I checked `stage3-pur-scalar-tensor-model-normalization`: its construction transports the strict-Roos-normalized tensor model to the supplied calculus and satisfies `IsTensorModelNormalized`, so I use its `T_E,T_L` transports for the fixed tensor comparisons. The repaired reduction node now states, for every normalized primitive scalar model, that `scalarReduction` is an isomorphism relative to `lem-pur-coefficient-extension-reduction-model`; its component is the explicit map from `(P ⊗ A_{E,n+1}) ⊗ B_{n+1}` to `P ⊗ B_{n+1}`, with both sides at the same index.

I then checked the exact stage3 limit-square statement: after instantiating its calculi, Roos models, scalar model and tensor models above, it gives `scalarTensorCompleted` followed by the tensor realization and the two scalarReduction maps as the route through `tensorReduction_E` and `derivedSigma`. I removed the redundant transport citation. The proof text now spells out the previously hidden passage: apply coherent reduction, use counit naturality and the derived-limit comparison from `lem-pur-scalar-extension-tower-coherence`, and cancel the invertible maps `gamma`, `gamma ⊗ (gamma ⊗ gamma)`, and the fixed tensor reduction comparison `r`. The repaired system node uses the fixed calculus supplied by `lem-coef-derived-system-evaluation-calculus` together with the K-flat-normalized closed symmetric tensor construction of `lem-sf-ringed-derived-closed-symmetric-monoidal`; its `systemClosed.monoidal` associator and the two nested `derivedSigma` composites are therefore pinned rather than arbitrary. The higher wrapper `lem-sf-coefficient-system-symmetric-calculus` reaches this item through an existing dependency cycle, so it is not added as a dependency.

For Step 2, I removed the unused good-pair descent citation. The rational-operation definition and rationalization definition directly supply localization of the prescribed integral maps and preservation of composition. Step 3 still uses their additive balanced pure-tensor and localized scalar-extension formulas. The fully-faithful coherent-reduction and integral tensor-constraint nodes remain the exact reflection and uniqueness inputs, and the two off-unit model-existence nodes are declared in `tool_uses`.

I checked identity, zero and ramified cases: identity scalar maps give identity quotient counits and comparisons, zero inputs give zero composites, and ramification changes only the recorded quotient map, never the level index. I ran LeanFinder, Loogle, Mathlib grep and LeanSearch for both changed new nodes; all queries and outputs remain in `searches.jsonl` and the node fields, with no project-specific Mathlib match. Every quote in `citations.json` is a verbatim substring of its cited statement. No Lean file, compiler, Lake, build, repository file or launcher file was written.

This repair addresses all four returned faults: explicit stage3 model instantiation and off-unit sources, explicit total-limit/counit cancellation, scalar-model-relative same-index gamma, and pinning the system associator to the K-flat-normalized calculus. The unused transport and descent citations were removed.
