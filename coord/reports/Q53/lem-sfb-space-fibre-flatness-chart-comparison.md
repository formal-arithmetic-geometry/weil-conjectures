# Stage-1 report: lem-sfb-space-fibre-flatness-chart-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-fibre-flatness-chart-comparison.json: existing statement, now split in nine steps; Mathlib verdict no match. No statement change.
- citations.json: fifteen step/node entries, each quoting the cited statement verbatim.
- searches.jsonl: five actual Q53 searches (LeanFinder twice, Loogle, LeanSearch, Mathlib grep). Earlier Q25 records in the node are preserved. The new hits concern scheme morphisms, not this algebraic-space quasi-coherent-module comparison. Read Mathlib/AlgebraicGeometry/Morphisms/Flat.lean, especially the Flat definition and base-change/composition instances, and SmoothFiber.lean:32-35; neither supplies this statement.
- report.md. No new nodes and no Mathlib leaves created. prepare.py is a sandbox-only assembly script, not part of the delivery.

## Attachments

None. Searched the live WeilConjectures tree for the exact blueprint id, fibre/fiber flatness, algebraic-space flatness and etale flatness. No declaration states every clause of this item. Scheme-level flat-fibre declarations do not supply an attachment.

## WANTED

None. All sources used are present under literature/stacks-project.

## What was wrong

The imported item had no proof. Its statement correctly expresses 05WY (2) iff (3), including all choices and diagram existence. Its blueprint ancestry has from.node null, as returned by blueprint_refs.py ancestor; preserved the existing detailed from.place/via and same_as []. Read the current latest blueprint's sk-thm-sf-ctf-stability unit and direct-image proof (3). The historical dependency chain through the finite-free locus is a supporting generic geometry input; no chapter/unit record or route was changed.

## Source error

Stacks spaces-more-morphisms.tex, Tag 05WY (lemma-flat-on-fibres-at-point), final paragraph, says both squares in its final comparison diagram are cartesian. The left one need not be. Explicit counterexample: let X=Y=Z=W=V=Spec(k), take U=Spec(k) disjoint union Spec(k), and choose u in the first component, with K=L=k. Then the top-left object U_w times_w Spec(L) has two points whereas X_z times_{Y_z}(V_w times_w Spec(L)) has one. All vertical chart maps are etale, as required. The assertion of the lemma remains true. Step 3 inserts the actual pullback D=X_z times_{Y_z} B and identifies A to D as etale; steps 6-7 first apply 05VW to D and then 05VU to the arbitrary chart A to D. No statement weakening is involved. STATEMENT-DISPUTED applies here to that sentence of the source proof, not to the item statement.

## Not duplicates

No new nodes. Searches of the whole DAG by titles, statements, Stacks tags 05WY and 05VW, fibre/flatness/chart words, and blueprint_refs.py searches 'flat on fibres', 'flat fibre', '05VW', and 'etale fibre flat' found reusable ingredients. In particular lem-sfb-space-pointwise-module-flat-base-change is the exact existing 05VW theorem, lem-sfb-space-module-flat-arbitrary-charts supplies 05VU, and lem-sfb-pointwise-module-flatness-base-change supplies the scheme theorem 047C. No clause of the item is renamed as a new node.

## Review by Q53

I read spaces-more-morphisms.tex Tag 05WY in full, its hypotheses immediately before the lemma, its diagram-existence paragraph, and especially its proof of (2) iff (3). I checked its references against spaces-morphisms.tex Tags 05VU and 05VW, more-morphisms.tex 047C, spaces-properties.tex 03FV and 03H4, spaces-topologies.tex 041F, sites-modules.tex 03D8, and the representable-property statements algebraic.tex 045B/045C and stacks-properties.tex 04XC. There are no new-node sources to review.

For step 1 I read the full statements of lem-a1-space-affine-etale-cover, lem-trf-space-fibre-products-etale-covers and lem-trf-space-chartwise-etale-permanence: they respectively supply scheme atlases surjective on point classes, the required algebraic-space fibre products and covering base changes, and composition of etale coverings. These give u over x without a finite atlas or quasi-compactness assumption. Step 2 uses only the explicitly stated common-extension equivalence relation of def-a1-algebraic-space-point-classes. It needs agreement over X, not just over Z; the definition gives exactly that, because both representatives have class x.

For step 3 I checked each projection: D=(X times_Y V) times_V B and A=U times_V B. The induced U to X times_Y V is etale by cancellation of two etale maps to X, so A to D is a scheme chart, not an asserted isomorphism. The two node statements used here supply existence of fibre products and all the etale permanence needed. Step 4 uses lem-sfb-space-module-pullback-quasicoherent for arbitrary morphisms, def-sfb-space-module-tensor-composition for its actual canonical tensor comparison, and lem-trf-scheme-zariski-etale-quasi-coherent-equivalence for its explicit arbitrary-scheme-morphism pullback comparison. Those statements do say these things. The scalar maps on the two realizations of N agree because they arise from the same map A to B, and the local tensor comparison multiplies the two scalar factors.

For step 5 I checked both flat base arrows separately. B to V_w is a field base change. B to Y_z has the three displayed factors; the first is a pullback of the etale diagonal W to W times_Z W, the second a pullback of V to Y, and the third a field base change. lem-pc-field-extension-flat states the spectrum-field-extension flatness itself and is an existing Mathlib leaf. lem-sfb-stack-chartwise-smooth-etale-calculus explicitly gives flat base change, composition and etale implies smooth implies flat, including algebraic-space representable morphisms. lem-trf-space-chartwise-etale-permanence supplies the diagonal's etaleness. No flatness of X to Y or of the module over Z was assumed.

For step 6 I read both clauses of lem-sfb-space-pointwise-module-flat-base-change: they give ascent under arbitrary base change and reflection when the base map is flat at the chosen point. This is applied to D, whose square really is cartesian, at the point constructed in step 3. For step 7 I read the complete statement of lem-sfb-space-module-flat-arbitrary-charts: it is some-chart iff every-chart, for a possibly nonsurjective source chart. This licenses the single point t of A over d and the identity chart B. Step 8 uses the two explicit clauses of lem-sfb-pointwise-module-flatness-base-change for schemes. The right-hand square is cartesian, its base arrow is flat, and the modules are quasi-coherent by step 4 and the Zariski-etale equivalence. Step 9 is the elementary transitivity of the proved equivalences, using existence from step 1. Every uses entry has a literal statement quote in citations.json; none uses a cited proof instead of its statement.

Small cases checked: F=0 (both conditions true); identity charts and K=kappa(u) (comparison reduces to ordinary field base change); the disconnected two-point source chart above (shows why the corrected chart step is essential); arbitrary nonalgebraic field extensions (the point equivalence and field-flatness lemma impose no algebraicity); empty spaces (there is no x to choose, so the fixed-point hypothesis is vacuous). No finiteness, Noetherian, nonzero-module or relative-flatness hypothesis entered. No non-elementary step exceeds 2000 characters. All new-node checklist items B1-B9 are vacuous except recorded item searches, precise source tags and preserved blueprint references. B10 was checked by the attachment search. C1-C4 were checked step by step above; C5 reuses existing nodes; C6 is submitted to the server DAG check; C7-C8 generic off-unit atlas/fibre-product/etale-permanence/Zariski-etale comparisons are explained in split_report.tool_uses. D1-D4 are avoided by the actual comparison construction and no new nodes; D5 is the common-field argument and corrected source diagram. E1-E6 are addressed by the pointwise hypothesis checks, explicit scalar comparison and small cases; E7 is the source error documented above. No SGA source is used.

## What remains unfinished

No mathematical part of this one-level split. Existing unsplit dependencies remain their own items. The required server dry run exited successfully: OK (not pushed), commit 5f84a483cdf, preflight passed. This includes the server DAG and split review checks. Delivery follows that successful dry run.
