# lem-sc-tangent-map-linear

Files written: `dag/nodes/sec-picard-framework/lem-sc-tangent-map-linear.json` (statement, split; Mathlib search found no match). No new nodes and no Mathlib leaves.

Attachments: none. The read-only Lean source has dual-number and rational-point tangent constructions, but no declaration tagged `lem-sc-tangent-map-linear` or stating this general residue-field formulation.

WANTED: `literature/stacks-project/varieties.tex`, Tags 0B2B and 0B2F, for `lem-sc-tangent-map-linear`. The local literature tree has only its indexes; I read the Stacks Project's published tag pages. Tag 0B2F states the claim and omits its proof. Tag 0B2B gives the pushout and the operations, so the written proof has `proof_origin.by = agent`.

The original node had an empty proof. Its statement agrees with Tag 0B2F after taking the base scheme to be `Spec k` and explicitly identifying the isomorphic residue fields. The proof supplies base-point preservation, scalar compatibility, and additivity. Its preexisting `blueprint.from.place` already locates the tangent-vector argument; the blueprint search found no same-statement node.

Unfinished work: none for this one-level split. The cited tangent vector-space node remains its own unsplit DAG item.

## Review by K1

I read Stacks Tags 0B2F (map on tangent spaces) and 0B2B (vector-space construction), the item, `lem-sc-tangent-space-vector-space`, and `lem-weil-pbc-residue-field-point-naturality`. Tag 0B2F requires the same residue-field equality that the item expresses as an isomorphism with a chosen identification. Tag 0B2B's dual numbers, reduction map, pushout, and scalar maps are exactly those in the item's cited vector-space node. No new node needed a separate source or small-case test.

Step 1 cites the naturality node's equation `g circ j_x = j_{g(x)} circ Spec(r)`. With `r` an isomorphism, identifying the two residue fields makes the canonical point of `x` compose to that of `y`. Associativity then shows `f circ theta` reduces to `j_y`. This is a functoriality statement, not something supplied by the residue-field definition alone.

Step 2 cites the vector-space node's explicit scalar formula using `m_lambda(epsilon)=lambda epsilon`. Postcomposition by `f` commutes with that fixed precomposition by associativity. Step 3 cites the same node's pushout uniqueness and its explicit addition formula. Because `f circ Theta` has the two required restrictions, it is the unique gluing for `f circ theta_1` and `f circ theta_2`; precomposition with `s` gives additivity. The final inference uses the step 1 well-definedness and these two vector-space laws.

I checked the hypotheses at their uses: `f` is a morphism of `k`-schemes, so postcomposites and the gluing remain over `k`; `y=f(x)` and the residue-field isomorphism enter step 1; the same field `kappa` is used for both scalar maps and both pushout constructions in steps 2 and 3. At `X=Y=Spec k` the map is zero between zero tangent spaces. For `A1 -> A1`, `t -> t^2` at the origin, dual-number vectors `t -> a epsilon` all map to zero, which respects both operations. For `t -> ct`, the map sends `a` to `ca`, matching scalar linearity. I found no false step to correct. The original missing proof is the correction.

For B-E: there is no new node to check for B1-B9, and searches of the DAG and whole blueprint found no duplicate claim. Every non-elementary fact in the proof has a citation, each cited statement was opened and quoted in `citations.json`, there is no dependency cycle or restatement node, and the argument uses no smallness, finiteness, or rational-point assumption. The off-unit residue-field naturality citation is an existing Mathlib leaf, used solely for its displayed naturality equation.
