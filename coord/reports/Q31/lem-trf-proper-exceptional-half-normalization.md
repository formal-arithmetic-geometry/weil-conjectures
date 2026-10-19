# Stage-1 worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proper-exceptional-half-normalization.json`: existing item, statement unchanged, now split in three steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.
- `report.md`: this review and delivery report. No Lean files, compiler, Lake, or build tools were used.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `/home/ubuntu/weil-newtargets-master/WeilConjectures/` for the exact blueprint tag, the item id, and exceptional-half/transpose terminology. No sorry-free project declaration states this item. The only relevant source is the parent blueprint proof and the existing DAG definitions.

## WANTED

None. The parent proof is available in `literature/blueprint/master/blueprint/sec-trace-formula/sk-c-proper-global/thm-trf-fixed-point-localization.md`, and all categorical inputs used here are existing DAG nodes.

## Corrections and retained work

The inherited statement, source, hypotheses, statement dependencies, blueprint ancestry and imported Mathlib search records are unchanged. The prior parent proof identifies this item as the exceptional-half calculation; I retained that route and made the specialization explicit: in the coefficient-pushforward definition take `f=a`, `g=q`, `b_1=id_Y`, and `c_1=d`, so `b_1 g = f c_1` is `q=a d`. No new node was created because the required facts are already stated by `prop-functor-package`, `thm-sf-comp-composition`, `def-trf-admissibility`, and `def-trf-coefficient-pushforward`. The item is not a Mathlib leaf: Mathlib searches returned generic adjunction and exponentiable-morphism declarations, none of which state this constructible exceptional formula.

The statement is not disputed. I checked the edge cases `a=id`, `d=id`, `K=0`, and an empty source: the formula reduces respectively to the exceptional counit/proper coincidence, the identity comparison, the zero map, and the unique map on zero objects. The source and target types agree after `j_q`, `alpha_{a,d}^{-1}`, `Ra_!`, and `j_a^{-1}`.

## Not duplicates

There are no new nodes, so no duplicate pair is introduced. I searched the whole DAG for exceptional-half normalization, adjoint transpose followed by counit, the tags and names of the four cited definitions/theorems, and for the key formula. The existing `def-trf-coefficient-pushforward` defines the general construction; the current item is its strict identity-leg specialization and normalization, while `lem-trf-proper-coefficient-adjoint` is a different proper-pushforward adjunction statement in another route. The item therefore cannot be replaced by either existing node.

## Mathlib searches

I ran the required `msearch.py` searches for this item and read every returned hit. LeanFinder and LeanSearch returned generic adjunction/mate and exponentiable-morphism formulas; the Loogle query with `Adjunction` was rejected as an unknown identifier; grep found generic CategoryTheory `counit` and composition occurrences. None states the finite-coefficient exceptional adjunction with proper coincidence and compact-support composition. The retained imported searches likewise found only ordinary module/site pushforward composition. No Mathlib declaration is claimed.

## Review by Q31

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the worker role and delivery-errors B--E, `SETUP.md`, `coord/dag-sync.md`, `GOAL.md`, the trace-formula chapter and `sk-c-proper-global` unit, the current item, its parent `thm-trf-fixed-point-localization`, and the parent blueprint proof in both master and main-20261015 snapshots. The item statement agrees with the parent sentence and preserves every hypothesis: separated finite-type morphisms, proper `a` and `q`, constructible exceptional adjunctions, finite-Tor outputs, and etale-origin witnesses.

Step 1 uses the exact exceptional-half clause of `def-trf-coefficient-pushforward`; after setting `f=a`, `g=q`, `b_1=id_Y`, `c_1=d`, its displayed `Xi_1` is the composition comparison followed by `Ra_!` of the exceptional counit. `prop-functor-package` states proper coincidence, and `thm-sf-comp-composition` states the canonical `alpha` and its identity normalization. `def-sf-etale-origin-subcategory` states the witness category required by the composition theorem. I checked that `q=ad` is the required equality and that the formula has source `Rq_*Rd^!K` and target `Ra_*K`.

Step 2 uses only the exceptional adjunction and transpose supplied by the two cited statements. `def-trf-admissibility` explicitly gives unit and counit satisfying both triangle identities. `def-trf-coefficient-pushforward` explicitly defines `delta` as the exceptional adjoint of the displayed compact-support composite. Applying the inverse transpose and the triangle identity gives the identity-leg counit followed by `delta`; the identity comparison is exactly the normalization stated in `thm-sf-comp-composition`.

Step 3 is elementary reassociation and substitution of the Step 1 expression into Step 2; no additional theorem is hidden. The displayed formula is copied exactly from the item statement, including the order of `j_a^{-1}`, `Ra_!(epsilon_d)`, `alpha^{-1}`, and `j_q`.

For the B--E checks, every non-elementary fact in Steps 1--2 is cited by a node whose statement I opened and quoted verbatim in `citations.json`; Step 3 is the only elementary step. No new node, duplicate, cycle, route replacement, SGA citation, or source error is present. Every step is below 2000 characters. The hypotheses and the identity/proper coincidence directions were checked on the edge cases listed above. The blueprint `from.place` and `same_as` metadata are retained, and the split report names the exact blueprint sentence realized.

## Unfinished work

None. The mandated server dry run and delivery are the remaining procedural actions.
