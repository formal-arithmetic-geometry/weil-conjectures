# Stage-1 delivery: lem-sfb-space-pseudocoherent-rhom-quasicoherent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-pseudocoherent-rhom-quasicoherent.json — split the unchanged statement by the etale-chart proof of Stacks 0A8A. Fresh searches found no Mathlib match.
- citations.json — fourteen entries, one for each step/node citation, copying its complete statement verbatim.
- searches.jsonl — actual search-command records; all five current searches succeeded.
- report.md — this report.

New nodes: 0. Mathlib leaves: 0. The sandbox initially contained only launcher brief markers, so there was no prior split or report to replace. I preserved the live node's original searches, source, creation and blueprint metadata and appended the current searches.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag and for pseudo-coherent/internal-Hom terminology. AlgebraicGeometry.pseudoCoherentRHomQuasiCoherent in AlgebraicGeometry/PseudoCoherentRHomQuasiCoherent.lean assumes a Noetherian scheme and an algebra source. AlgebraicGeometry.rhom_supported_quasiCoherent and its separate perfect/pseudo parts are also scheme statements. Even where their displayed proofs are sorry-free they cannot attach to the arbitrary algebraic-space statement here. Their DAG nodes are reused in the proof on Zariski charts.

## WANTED

None. All mathematical sources needed are in literature/stacks-project. The historical coord/dag-sync.md mentioned in the inherited brief is absent; the current user brief identifies the live read clone, which I used.

## What was wrong or incomplete

The item was an unsplit statement with no proof; its statement agrees with 0A8A, with the explicitly intended etale-local extension of the bounded-below clause. There is no statement dispute or change. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor prints None. I retained that inherited ancestry and documented the full place in split_report.blueprint rather than inventing an ancestor or changing other nodes. I read both the recorded unit and the newest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images proof. This coherent-duality input is a generic tool under the inherited direct-image route; it does not replace a unit step. The latest unit text has changed from the old imported record, but does not alter the local algebraic-space assertion.

The existing lem-sfb-zariski-etale-pseudocoherent-rhom only states case (1) of 08JP. It cannot be cited for a perfect source and an unbounded target. I corrected that potential citation gap by writing the finite strictly-perfect computation in step 4, using the existing ringed-site model theorem. No duplicate perfect comparison node was created.

## Not duplicates

No new nodes. I searched the whole DAG by 0A8A, 08JP, source labels and internal-Hom/restriction concepts, and the whole imported blueprint via blueprint_refs.py search (including perfect Hom, internal Hom quasi, 08JP and quasi-coherent Hom). The scheme-only 0A6H nodes do not state the algebraic-space item. The existing generic strict-perfect model makes the remaining perfect comparison elementary, so a new 08JP case-(2) node would be unnecessary.

## Review by Q16

I read spaces-perfect.tex lemma-quasi-coherence-internal-hom (0A8A), including its complete proof, and then the four reductions it names: lemma-check-quasi-coherence-on-covering (08F2), lemma-descend-pseudo-coherent (08HE), lemma-descend-perfect (08HG), and lemma-descend-RHom (08JP), both cases and proofs. I also read lemma-epsilon-flat (08H8) and lemma-derived-quasi-coherent-small-etale-site (071Q). For the scheme conclusion I read perfect.tex lemma-quasi-coherence-internal-hom (0A6H), all four clauses and its proof. For the finite calculation I read sites-cohomology.tex lemma-Rhom-strictly-perfect (08JH), lemma-Rhom-complex-of-direct-summands-finite-free (08JI), and lemma-restriction-RHom-to-U (08JB). Finally I read spaces-properties.tex lemma-properties-quasi-coherent (03M1), its six clauses and descent proof. There are no new nodes whose sources need a further review.

Step 1 uses the actual statement of lem-sfb-space-derived-etale-chart-calculus: etale restriction is exact, preserves quasi-coherent cohomology, and detects it on a jointly surjective scheme cover. Thus it preserves the specified lower bound on each chosen chart. The statement of lem-sfb-space-qcoh-kernels-colimits gives kernels, cokernels, images and finite sums in all module sheaves; applying these to the local finite-free/split finite-free models proves that K has quasi-coherent cohomology. This extra check is needed before invoking a derived quasi-coherent equivalence, rather than silently assuming that K belongs to its domain.

Step 2 uses the full equivalence in lem-sfb-derived-etale-zariski-equivalence for K and L, already in its quasi-coherent domain, and its stated exactness and faithfulness to reflect the lower bound. The other two cited statements give respectively perfectness and pseudo-coherence of the Zariski preimage. The equivalence of the item's model condition with the m-pseudo-coherence condition required for the latter is used only in the easy direction: stupidly truncate a bounded-above finite-free model at m. The inclusion induces isomorphisms above m and a surjection at m. Local restrictions and refinement preserve this condition directly.

Step 3 cites the exact scheme conclusions lem-sc-rhom-supported-qcoherent-perfect-part and lem-sc-rhom-supported-qcoherent-pseudo-part. The former assumes no lower bound, the latter assumes precisely the chartwise bound proved in step 2. Neither requires Noetherianity. I did not use the more specialized Noetherian algebra-module statement found in Lean. These two scheme results are declared off-unit tools in split_report.tool_uses; they supply the analogue for schemes explicitly cited in the source proof.

Step 4 is elementary relative to the cited lem-sfb-ringed-site-strict-perfect-hom: that statement says ordinary Hom out of a bounded strictly perfect complex sends the fixed K-injective augmentation to a quasi-isomorphism for arbitrary targets. Therefore it supplies a genuine derived model on both ringed sites, not merely a formal Hom definition. The remaining comparison is the identity on finite powers for a free term, restricted to a split idempotent for a summand, summed over finitely many source degrees. It commutes with both compositions in the Hom differential. Exactness of epsilon pullback is in the equivalence node's statement, and the stated slice Hom comparison of lem-weil-pbc-ringed-internal-hom-exact-restriction justifies checking locally. This is a finite calculation rather than a hidden derived comparison theorem; no target bound is smuggled into case (i).

Step 5 uses exactly the displayed derived-category isomorphism of lem-sfb-zariski-etale-pseudocoherent-rhom, only in the pseudo-coherent case. Its scheme, pseudo-coherence and uniform-on-this-chart lower-bound hypotheses have all been verified. The equivalence node then gives quasi-coherence of epsilon pullback of the scheme Hom. Step 6 uses the general ringed-site slice Hom isomorphism from the restriction node; its statement covers arbitrary unbounded objects, and an etale chart is an object of the small site. The chart-calculus node then detects quasi-coherence on that jointly surjective cover. This checks each actual use against a statement, not against another node's proof.

I checked the small and boundary cases: the empty algebraic space or a zero source/target gives zero Hom; rank-zero summands and empty finite degree intervals cause no problem in step 4; the perfect case permits completely unbounded L; a non-quasi-compact space can have unrelated lower bounds on its charts, and the proof never takes a minimum over them. Local finite free models need no Noetherian or separation assumptions. Exactness plus faithfulness, not exactness alone, is used to reflect vanishing in step 2. I checked transitive statement/proof dependencies of all cited nodes: none leads back to the item.

Against delivery-errors B--E: no new elementary, duplicate, or clause-restating nodes; no unsupported tags replacing citations; every step's non-elementary inputs are existing cited statements; proof_deps is exactly their union; all notions in the unchanged statement retain their definition citations. Every step is shorter than 2000 characters (the longest is 1117), and the elementary perfect comparison explicitly gives the underlying finite calculation. All recorded searches were run through msearch.py and their hits were read; none states this theorem, and no failed service is reported as absence. No SGA source, Lean edits, compiler, or local checker was used.

## Unfinished work

None in the one-level split. The existing unsplit dependencies remain their own future stage-1 items. Server validation and delivery are recorded below when completed.
