# Stage-1 report: lem-trf-verdier-contraction-factorization

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-verdier-contraction-factorization.json` — statement, split proof; no new node and therefore no Mathlib leaf.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.

Attachments: none. I searched the slopmaster2 source and found no declaration tagged `lem-trf-verdier-contraction-factorization`; the related `Pairing.lean` declarations define the operations but do not prove this comparison.

WANTED: none.

What was checked and corrected: the imported item is exactly the factor-exchange comparison in Step 3(c) of `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-trace-class/lem-trf-trace-class-diagonal-pairing.proof.md`. I retained its statement and existing coefficient/admissibility hypotheses. The proof is split into the signed expansion of the pulled-back contraction, the tensor--Hom transpose formula for the Künneth--Verdier map, comparison of exceptional adjoints using the exceptional Künneth counit formula, and uniqueness/coherence. No clause of the item was restated as a new node, and no duplicate node was created.

## Review by Q66

I read the item node, the current `sk-d-trace-class` unit record, the `sec-trace-formula` chapter record, and the complete main-20261015 proof of `lem-trf-trace-class-diagonal-pairing`, including the paragraph defining `gamma^tau`, `varpi`, and `r`. I also read the complete statements of `def-trf-supported-pairing`, `def-trf-dualizing-complex`, `def-weil-derived-pullback-tensor-hom`, `def-sf-kv-maps`, `def-trf-admissibility`, `thm-trf-dualizing-complex-composition`, `lem-trf-kv-evaluation-formula`, `lem-trf-exceptional-kunneth-counit`, and `prop-functor-package`.

Step 1 uses the supported-pairing statement for the four-factor order and contraction, the dualizing-complex statement for the evaluation maps, the derived pullback/tensor statement for the signed tensor operations, and the Künneth-map definition for the specified exceptional product; the composition theorem supplies the target identification `Rp_1^! omega = omega_Z`. I checked that after factor exchange the factors are `(K_2,D_1,K_1,D_2)`, that `r` sends them to `(D_1,K_1,D_2,K_2)`, and that the two evaluations have the required source order.

Step 2 specializes `lem-trf-kv-evaluation-formula` with both schemes and both coefficient objects equal to `X,K`. Its statement explicitly identifies the tensor--Hom transpose with the evaluation composite followed by `alpha_{id_X,a_X}`. I checked that the item’s `P` is the lemma’s `B`, that `Lp_2^*K` is its `U`, and that the signed reassociation is the one in the stated formula.

Step 3 uses the exact exceptional-adjoint formula in `lem-trf-exceptional-kunneth-counit` with `f_1=f_2=a_X` and `L_1=L_2=A_s`. The projection-formula and compact-support composition clauses of `prop-functor-package` identify its product of counits with the adjoint defining `varpi` after the Step 2 composite. I verified that every map is applied in the finite-Tor constructible domain guaranteed by `def-trf-admissibility`, and that the final target is transported by `thm-trf-dualizing-complex-composition`.

Step 4 invokes the adjunction bijection and the coherence of the specified projection, composition, exchange, and signed tensor maps. I checked that the only permutation is the displayed `r`, so the Koszul signs are exactly those already present in the derived symmetric monoidal constraints. All quotes in `citations.json` are copied verbatim from the cited node statements. No statement error or hidden additional hypothesis was found.
