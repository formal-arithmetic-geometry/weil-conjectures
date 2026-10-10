# Delivery report

Files written: the repaired item `dag/nodes/sec-curve-estimates/lem-sc-separated-affine-function-field-surjective.json` and the new unsplit statement node `dag/nodes/sec-curve-estimates/lem-sc-local-domain-dim-one-principal-localization-fraction-field.json`; updated `citations.json`.

Attachments: none.  WANTED: none.

The return concerned four uncited ingredients in Step 1. I repaired each one: the canonical morphism from `Spec(B)` and its image of generalizations, base change of the open immersion, the principal-open description and localization to `K`, and the affine fibre product over `Spec(Z)` with ring `A tensor_Z B`. The new node records the one-dimensional local-domain localization fact as a statement-only node, based on Stacks Algebra Tags 00CM and 00C8. The existing prime-localization node supplies the prime correspondence used in its application.

## Review by J1

I reread Stacks Varieties Lemma 09NB (the opening paragraph and the separatedness sentence), and the statements of every node cited by all three steps. Step 1 now cites `lem-weil-pbc-spec-local-ring-canonical-morphism` for the canonical map and the fact that its image is the generalizations of `x`; `lem-weil-pbc-open-immersion-base-change` for identifying the pullback with the open subscheme on `c^{-1}(U)`; `lem-weil-pbc-principal-localization-open-immersion` for `D(f)=Spec(B_f)`; `lem-weil-pbc-primes-of-localization` for the prime correspondence; the new node for `B_f` being the fraction field; and `lem-weil-pbc-fibre-product-affine-spectra` for `Spec(A) x_{Spec(Z)} Spec(B)=Spec(A tensor_Z B)`. The quoted statements in `citations.json` are verbatim portions of those node statements. I checked the hypotheses: `B` is a local domain of dimension one, so a nonzero element of its maximal ideal exists and the only prime avoiding it is `(0)`; the standard `P^1` chart remains a small test case.

Step 2 uses the separated diagonal definition, closed-immersion base change, and the affine fibre-product statement; all three cited statements explicitly provide those constructions. Step 3 uses clause (1) of the affine closed-immersion criterion and the same affine fibre-product statement, giving surjectivity of the global-sections map `A tensor_Z B -> K`. The off-unit canonical-local-ring node is declared in `split_report.tool_uses` because Step 1 takes its morphism and image statement as a generic tool from the proper-base-change unit. The prime-localization and fibre-product nodes are Mathlib leaves, so they require no tool-use declaration.

For the new node I searched the DAG and blueprint for an existing one, then recorded LeanSearch, Loogle, and Mathlib-source grep searches. No exact Mathlib theorem states the one-dimensional local-domain specialization, so it remains unsplit. I also checked the new statement on `B=k[t]_(t)` with `f=t`, where `B_f=k(t)`, and on a DVR; both agree with the claim.
