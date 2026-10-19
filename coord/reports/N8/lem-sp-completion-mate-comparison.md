# Worker report: lem-sp-completion-mate-comparison

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-completion-mate-comparison.json`: existing item split in ten proof steps; status set to `split`; no new nodes.
- `citations.json`: verbatim quotations for every cited node in every proof step.

## Attachments

No finished declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states the item or carries the blueprint tag. The only similarly named completion-mate declaration is absent from that source tree. The archived Lean declarations and the imported node's `lean_audit` were treated as reference metadata only; no Lean declaration was attached.

## WANTED

None. The proof follows the local Stacks sources and the blueprint source named in the item. No literature was downloaded and no Lean or compiler command was run.

## What was wrong or incomplete

The shared node was an earlier complete split but still had status `unsplit`; I retained its statement, ten-step proof, dependency list, blueprint ancestry, search log, and review metadata and changed only the stage-1-owned status to `split`. I found no statement correction, source error, duplicate, or missing dependency. The item is an agent-supplied comparison theorem from `fix-lem-exchanges` Proof Step 4, so its proof explicitly constructs the strict quotient tower, normalizes the diagonal adjunction, proves the projection comparison, identifies the diagram exchange, and transports the mate identity through completion. The square has no properness, smoothness, constructibility, or étale-origin hypotheses, as required by the statement.

## Review by N8

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `coord/delivery-errors.md` (B–E), `coord/dag-sync.md`, `GOAL.md`, the fixed chapter `sec-smooth-purity`, the unit `sk-prop-sf-cbc`, and the item source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/fix-lem-exchanges.md`. The source places the item in Proof Step 4 as the missing integral comparison between the finite strict-tower exchange and the completed adjunction. I also read the full item statement and all ten proof steps in the current DAG.

Step 1 uses the diagram-site realization, K-flat resolution, levelwise-abelian tower, K-flat-complex definition, derived-tensor descent, and ringed-topoi pullback comparison. Their statements supply respectively the small diagram site, a single flat-term K-flat representative, levelwise acyclicity, the tensor criterion, descent to the strict quotient tower, and the canonical pullback/tensor maps. The step therefore constructs actual tower objects and maps, rather than a family of unrelated level maps.

Step 2 uses levelwise abelian towers, preservation of K-injectives by the relevant right adjoint, existence of K-injectives, the total-derived K-injective computation, the strict-tower homotopy-limit comparison, the pre-derived adjunction fraction characterization, the ordinary mate definition, and the completed pullback adjunction. I checked the terminal-object argument for `ev_1 ⊣ Δ`, the diagonal direct-image and limit identifications, and that the derived units and counits are the normalized diagonal ones; the completion unit is exactly the image of the diagonal-to-quotient-tower map.

Step 3 uses the tower pushforward/limit comparison, ringed-topoi tensor pullback, pre-derived adjunction, projection-formula arrows, projection-formula totalization, and levelwise abelianity. The finite perfect quotient hypothesis is used only to invoke the finite-projective projection formula. Evaluation at each `n` is the ordinary `P_n` projection isomorphism, and zero cohomology of the cone gives invertibility in the derived tower category. No finiteness of `P_n` or boundedness of the input is silently added.

Step 4 uses the tower pushforward/limit comparison exactly for `a_{u,N}:Ru_* L_U N ≅ L_V R_u^T N`, with its K-injective normalization and compatibility with projections. Substituting `u=f'` and `N=G_{g'} R_X K` gives the statement's map `t`; the constant-tower specialization is the identity on a diagonal K-injective representative.

Step 5 uses the exchange/tensor-coherence node. On the four diagram sites, its two displayed composites identify `v H` with `H' R_{Y'}(e)` before any inverse limit or evaluation. I checked that the coefficient diagram is pulled back termwise and that the exchange on diagonal objects is the diagonal of the ordinary mate from Step 2.

Step 6 uses the projection-mate-exact node, the tower pushforward/limit comparison, the strict-tower homotopy-limit node, and the completion pullback-adjunction node. Naturality in the quotient-unit maps gives the normalized unit equation after applying `L`; the cited statements provide the required mate/projection normalization and the completion unit. This is a genuine comparison of the specified maps, not an appeal to equality after evaluation.

Step 7 uses the pre-derived adjunction fraction characterization, the tower pushforward/limit comparison, the strict-tower homotopy-limit comparison, the ringed-topoi composition comparison, and the completed pullback adjunction. The direct-image composition maps and their diagram analogues are identified on K-injective representatives, and the mate bijection transfers the resulting unit equation to the completed mate.

Step 8 uses the ringed-topoi composition comparison, tower pushforward/limit comparison, pre-derived adjunction, strict-tower homotopy-limit comparison, and completed pullback adjunction. The counit equation follows from the same normalized composition comparison and the mate formula. I checked that both unit and counit equations are stated before the final naturality argument, so no hidden criterion on evaluated towers is used.

Step 9 uses the projection-mate-exact node, ringed-topoi composition comparison, and completed pullback adjunction. The canonical projection comparison is the mate of the displayed completed unit/counit composite; substituting the normalized unit equation yields `t ∘ E^c = L(v) ∘ s` by the adjunction hom-set bijection. The source and target are exactly those in the item, with all comparison isomorphisms fixed.

Step 10 uses the strict-tower homotopy-limit comparison, finite-restriction/evaluation normalization, and the completed pullback adjunction. Applying finite-coefficient restriction to the already established tower identity gives the ordinary `P_n` adjunction mate; the evaluation maps commute with the fixed comparison maps by their stated normalization. This verifies the final clause without assuming evaluation is conservative.

I opened each cited node from `dag/nodes` and generated `citations.json` from its exact current `statement` field, so every quotation is verbatim and each step's non-elementary fact is explicitly cited. The proof dependency union equals the uses in the ten steps. I checked edge cases: the zero complex, `I=0` (constant quotient tower), `P_n=0`, identity square, and empty/small sites; all maps reduce to the corresponding identity or zero comparison and no step adds a geometric hypothesis. The item has no new helper nodes and hence no duplicate pair to record. No source or DAG file outside this sandbox was modified.
