# Stage-1 delivery: lem-trf-section-local-dualizing-comparisons

## Files written

- dag/nodes/sec-trace-formula/lem-trf-section-local-dualizing-comparisons.json: existing statement, now split into eight steps; Mathlib search found no match.
- citations.json: one verbatim statement excerpt for each of the 25 step/node citations.
- report.md: this report.

No new nodes; no Mathlib leaves created. No Lean written or compiler invoked. The shared repository was only read.

## Attachments

None. I searched lean/WeilConjectures by the exact blueprint id and by dualizing/section/purity concepts. The nearby AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor (WeilConjectures/SixFunctors/Etale/Derived/SmoothDuality.lean:77) has a sorry and does not supply the deformation comparisons. Its sorry-free tensor corollary supplies only part of a different assertion. The pro-etale dualizing definitions concern a different site. There is no complete attachment for this item.

## Literature and searches

Read the current blueprint's sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md, opening paragraph and Local construction, together with the chapter and sk-i-curve-zero unit records. The item realizes a local input to that unit's normal-cone argument, not its statement, so no unit realization fields change. Also read the affine-space ambient adjunction statement and proof in the older blueprint and the current ordinary-etale adjoint locality and smooth exceptional base-change proofs. The item follows the blueprint and is consequently marked proof_origin.by = agent. No SGA source is used.

Ran the required msearch.py LeanFinder, Loogle, grep and LeanSearch commands, and a second LeanFinder phrasing. All services answered. Read their hits: smooth coordinate algebra, affine-space maps, sheafification adjunctions, and structure-sheaf module pushforward adjoints do not state an ordinary-etale compact-support dualizing comparison. Retained the item's inherited search records and appended the exact current logged queries/results. The second phrasing found pushforward right adjoints for structure-sheaf modules, not right adjoints to compactly supported etale pushforward. No new claim of a Mathlib match is made.

Searched the whole DAG for centred coordinates, exceptional base change and section dualizing comparisons, and used blueprint_refs.py ancestor and searches 'section dualizing', 'dualizing line', and 'normalized section'. The DNC theorem and orientation-chart node have different coefficient/base hypotheses and include global gluing or orientation assertions. The existing finite-ring centred-coordinate and Rees-base-change nodes are the needed geometric inputs. No duplicates are created.

WANTED: none.

## Corrections and remaining work

No statement change or statement dispute. The seeded node had no proof. Its statement dependencies are retained because the statement explicitly fixes the corresponding constructions and notation. Proof dependencies now name exactly the union of step uses. No new assumptions on regularity, boundedness, constructibility, or coefficient fields are introduced. The proof does not use the section-coordinate-counit-normalization sibling to assert that the initial comparison is already normalized: it proves the correction required here directly. Nor does it use the stronger global section-specialization theorem.

No unfinished part of this item's split remains. Its cited unsplit nodes remain separate stage-1 work; this delivery does not claim that those nodes have already been proved in Lean.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs.

## Review by Q126

I checked delivery-errors B through E against the actual node statements. For the item I read the current DNC proof through the correction at one, stopping before gluing. There are no new node sources to check. For the imported geometric inputs the existing centred-coordinate statement gives the Cartesian square of centres, affine bases and separated etale charts; its source identifies Stacks 054L (lemma-smooth-etale-over-affine-space), 024T (proposition-properties-sections) and 067U (lemma-immersion-smooth-into-smooth-regular-immersion). The Rees statement gives both the arbitrary-base-change and etale-map-of-pairs assertions used here. I did not replace either of these geometric assertions by a definition.

Step 1 uses precisely the Noetherian finite-type theorem, the smooth-tensor theorem's shifted rank-one assertion, and exact module inverse image. I checked that the base of q is Noetherian, that both structural maps have the required compactifications and dimension, and that finite-ring annihilator invertibility persists under pullback. Pulling back a sheaf and its trivializing cover gives the stated section lines without identifying fibres arbitrarily.

Step 2 uses the full canonical-map assertion of prop-asd-smooth-base-change, not merely an abstract isomorphism. Its statement explicitly transposes the pulled-back counit and permits arbitrary Noetherian base change in the entire ordinary unbounded category. The two fibre squares and sections give the stated maps after exact inverse image and the module-linear composition isomorphism. I checked that the fibres have the assumed compactifiable structural maps. The map type is i_r^*F to the fibre section dualizing object, in the required direction.

Step 3 uses the centred-coordinate statement for charts whose inverse zero locus is scheme-theoretically the section. The separated finite-type base-change statement provides the same properties for V_i and the family restrictions. The Noetherian finite-type theorem and Nagata's explicit 'in particular' clause justify applying the later locality maps to chart composites. Open chart inclusions are etale by the cited open-immersion theorem. Their finite type follows from quasi-compactness of opens in Noetherian schemes; their separation follows from the diagonal of an open immersion being an isomorphism. The polynomial affine spaces are separated finite type directly from their finitely generated coordinate rings and diagonal equations. All Nagata bases used here are affine Noetherian, hence quasi-compact and quasi-separated.

Step 4 uses the affine-space theorem on the full unbounded ordinary categories, and the statement of det-sp-unique-right-adjoint, which explicitly supplies the unique comparison compatible with counits. I checked the direction of the counit equation before restricting to A and the zero section. The finite Tate pullback statement supplies the zero-section twist identification, including d=0.

Step 5 applies the smooth base-change statement for base restriction, then the etale locality statement twice to the same structural composite g_i u_i = p_i e_i. The locality node says u^* f^times K is canonically isomorphic to (fu)^times K. It therefore gives exactly the two objects identified in the step. The separate unique-right-adjoint statement fixes the counit comparison, and the module compositor identifies the section pullbacks. This proves the chart identification rather than assuming a smooth orientation theorem beyond the cited adjunction.

Step 6 checks the standard deformation model by an explicit monomial calculation over an arbitrary ring, so no domain or reducedness is required. The Rees statement gives etale maps of the two pairs and base restriction, preserving the sections. Their deformed maps are base changes of the original separated etale finite-type maps, so the Step 3 hypotheses apply. The other citations are the same smooth base restriction, locality, counit uniqueness, and section compositors as Step 5. The affine-space conclusion follows from Step 4 over the polynomial Noetherian base. This is one application of previously stated geometric and adjunction inputs, not a hidden new lemma. All proof steps have fewer than 2000 characters.

Step 7 is the explicit three-isomorphism composite using Tate pullback. Its sole external assertion is precisely the canonical pullback formula in the cited Tate statement. Step 8 uses the inverse-image compositor to type the automorphism h, then writes h^{-1} h theta = theta. This is elementary cancellation and functoriality, not a new node for a clause of the item. Neither step assumes an equality with a separately chosen orientation.

I tested d=0 (empty coordinate tuple, identity affine adjunction, zero twist), empty S, and the zero coefficient ring (a free rank-one module over the zero ring is still the coefficient module). The Rees injection does not cancel ring coefficients, and the normalization only inverts isomorphisms already supplied. No field or nonzero-ring hypothesis is used. I checked transitive dependencies of every proposed external proof input for a return path to this item; none exists. Off-unit infrastructure is declared only in split_report.tool_uses for maintainer review, preserving the trace-formula unit's route.
