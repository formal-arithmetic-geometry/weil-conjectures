# Q56 stage-1 report: lem-coef-kan-fibration-arbitrary-base-fibers

## Files written

- dag/nodes/sec-six-functors/lem-coef-kan-fibration-arbitrary-base-fibers.json: the assigned statement, split into six proof steps; no Mathlib match.
- citations.json: nine entries, one for every step/node citation, copied verbatim from the cited statements.
- report.md: this report and the author's review.

No new DAG nodes and no Mathlib leaves. prepare.py and searches.json are local sandbox preparation/search records, not delivery files.

## Attachments

None. Exact-id, blueprint-tag and notion searches (KanComplex, KanFibration, kanFibration and Kan fibration) under /home/ubuntu/weil-src-slopmaster2/WeilConjectures returned no declaration. The upstream master was also searched as reference material; no finished proof was claimed from it. The item has no recorded Lean declaration to attach.

## WANTED

WANTED: archival copy of Kerodon Proposition 3.3.7.1 (00ZN), for lem-coef-kan-fibration-arbitrary-base-fibers. Read online at https://kerodon.net/tag/00ZN on 2026-10-17.

WANTED: archival copy of Kerodon Proposition 3.2.8.1 (00XC), for the component-action and exact-sequence argument of lem-coef-kan-fibration-arbitrary-base-fibers. Read online at https://kerodon.net/tag/00XC on 2026-10-17.

These are Kerodon tags, not Stacks tags. No Stacks theorem is substituted for a homotopical result. Nothing was downloaded or written to the repository's literature directory.

## What was wrong

The previous worker's missing-node diagnosis is stale: the shared DAG now contains the assigned item, sourced to Kerodon 00ZN, with chapter sec-six-functors and unit sk-prop-sf-biduality-general. This report replaces that diagnosis. The mathematical statement is unchanged: no Kan-base hypothesis, no extra nonemptiness or connectedness assumption, and both directions remain.

The imported item had no proof. The new proof realizes the orbit/sequence argument of 00XC using the existing arbitrary-base realization theorem. It does not silently treat B, E or T as Kan and does not invoke the item to justify its own strict-fiber comparison. Kerodon's published 00ZN proof uses Ex-infinity instead; this expanded argument is marked proof_origin.by = agent. The stage-1 node level permits this choice below the fixed unit route. No chapter/unit binding or target statement was changed.

## Not duplicates

No new nodes were created. Existing candidates were read: lem-coef-spaces-homotopy-fiber-detection assumes all four simplicial sets Kan and concerns homotopy fibers; lem-coef-space-kan-fibration-fiber-criterion tests one fibration between Kan complexes for contractible fibers; lem-cbc-kan-fibration-fiber-criterion tests one fibration for being trivial. None is the strict-fiber comparison of an arbitrary map of two Kan fibrations over a possibly non-Kan base. Their proofs were not cited as if they were statements.

DAG searches included 00ZN, Kan fibrations, fiber and weak-equivalence terminology; blueprint_refs.py ancestor gives prop-coef-integral-exceptional-adjoint, while searches for the full arbitrary-base title, Kan and fiber give no blueprint node stating this item. The broad fiber search returns geometric/coefficient nodes, not this homotopy-theoretic criterion. Thus blueprint.same_as remains []. The current main-20261015 ancestor proof was read: the technical input belongs below paragraph 2's displayed derived mapping-complex / inverse-limit calculation and its enhanced-adjunction ancestry. All four proof dependencies have the same unit as the item; no off-unit tool use is needed.

## Review by Q56

I read Kerodon 00ZN and 00XC online. In 00ZN the vertical maps are Kan fibrations and no objects are assumed Kan; taking its base map to be the identity gives exactly the item. It phrases the fiber conclusion as a homotopy equivalence of Kan complexes. The item uses weak homotopy equivalence, and the proof here proves exactly that realization-based version directly, without silently needing a separate Whitehead theorem. I also read the full statements of all four cited nodes, rather than their titles or only their proofs.

Step 1 uses lem-coef-kan-realization-serre's sentence that every Kan fibration realizes to a Serre fibration, explicitly without Kan assumptions on source/target. It uses lem-coef-realization-finite-limits's natural pullback homeomorphism for the actual strict vertex fibers and the actual map u_b. It then uses lem-coef-serre-homotopy-exact-sequence for natural exact sequences, path lifting, actions, orbit sets and stabilizers. Each of those clauses occurs in that node's statement. Fiber Kan-ness is proved by lifting a horn over the constant base simplex, not taken from an unrelated definition node. The empty-fiber discussion uses the path-lifting clause to show that the corresponding total-component fiber is empty, so no nonexistent basepoint is selected.

Step 2 uses the weak-equivalence definition stated by lem-coef-kan-quillen-right-proper and the action/orbit/stabilizer clauses of the Serre node. The square is over the identity, so the acting group is literally the same on both sides. Bijectivity on total components gives bijectivity on orbit sets. Isomorphism on total fundamental groups gives equality of stabilizers; the coset calculation then gives bijectivity on each orbit. Thus it does not confuse an orbit bijection with a bijection on the underlying component sets. This also handles F empty without choosing e.

Step 3 uses the Serre node's exactness and naturality only. I checked the kernel chase through pi_(n+1) of the base and the cokernel adjustment by the boundary image. The product a' (f_* a)^(-1) is corrected by multiplying (boundary c) a on the left. This order works for n = 1; no abelian five-lemma assertion is used. The total-space group isomorphisms here are exactly the assumed weak equivalence at the fiber vertex and its image.

Step 4 uses the same node's equivariance and orbit formula. An equivariant bijection has an equivariant inverse, hence gives a bijection on orbit sets over every component of the base. Every realized point lies in a simplex joined to a vertex, so choosing a vertex per component does not require B Kan. The empty orbit sets remain empty. These statements give precisely the asserted total-space component bijection.

Step 5 uses group exactness and naturality in the Serre node, with fiber isomorphisms from the hypothesis. I checked separately the surjectivity case n = 1: the boundary lands in pi_0 of the fiber, so the argument uses the fiber component bijection and pointed-set exactness, not a group structure on pi_0. The injectivity argument uses the boundary from pi_(n+1) and fiber group injectivity. All multiplication adjustments have the correct order in the fundamental group.

Step 6 uses the realization-based weak-equivalence definition in lem-coef-kan-quillen-right-proper. The elementary argument moves a basepoint inside its representing simplex to a vertex, describes the cube-collar transport and its inverse from the reverse path, and observes that this commutes with the map. This covers all basepoints, rather than only vertices. If B has no vertices it has no simplices and forces both total spaces empty; the unique map is then the identity. No unproved homotopy-fiber identification, fibrant replacement comparison or finite-limit computation is hidden in this step.

For delivery-errors B1-B10: no new node is introduced, so there is no statement-only, hollow-definition, source-tag or leaf-record problem in a child. The item keeps its self-contained statement and existing notion dependency; its proof supplies rather than relabels the argument. All new searches ran with msearch.py. Successful result text is recorded exactly, including two semantic phrasings, a valid Loogle query, grep and LeanSearch. One earlier Loogle attempt rejected the identifier WeakEquivalence; that failed attempt is recorded as unavailable, not evidence of absence. I read the matching source signatures in Mathlib CategoryWithFibrations.lean, Over.lean, Bifibrant.lean and Instances.lean: horn lifting, inherited weak-equivalence predicates and stability of trivial fibrations do not state the criterion. Existing historical searches were retained. No Mathlib leaf was fabricated.

For C1-C8: the four non-elementary tools are all existing nodes and their statements supply the exact clauses used above. citations.json gives a verbatim quote for every use. Every proof_deps entry occurs in a step and conversely. The dependency graph was followed from all four tools; none reaches this item, so adding these edges introduces no cycle. They all have unit sk-prop-sf-biduality-general. No proof-only implementation detail from another node is required.

For D1-D5: zero new nodes, explicit argument in the item, both implications with each induction-free diagram chase written out. There is no lemma restating a clause, and no appeal to an unspecified standard five lemma. For E1-E7: Serre realization is valid over arbitrary simplicial bases by its cited statement; realization preserves the needed actual finite pullbacks; the exact-sequence theorem assumes neither connectedness nor surjectivity. I tested B empty; B a point; disconnected/discrete B with a missing component; identity maps; E and T both empty over a nonempty B; empty E mapped into nonempty T (both sides of the criterion false at an occupied vertex); and products B x K -> B with B = Delta^1, which is not Kan. The claim and argument behave correctly. No source error or statement dispute was found, and no SGA source is used.

## What could not be finished

No unfinished mathematical points. The required validation is the server-side deliver.py --no-push dry run; READY is reserved for its OK result. The sandbox is left for the independent second reader, and this worker makes no push.

## Second reading by Q56

This independent reading opened Kerodon Proposition 3.3.7.1 (00ZN) and Proposition 3.2.8.1 (00XC), the full statements of the four cited nodes, the three duplicate candidates named above, and the current main-20261015 blueprint ancestor's proof paragraph 2. The source is Kerodon, not a Stacks theorem. The item keeps both directions, arbitrary small B, both Kan fibration hypotheses, the strict commutative square and every vertex fiber. Its realization-based weak-equivalence formulation is proved directly, so the source's homotopy-equivalence wording for Kan fibers introduces no unproved Whitehead step.

- Step 1: checked against the horn-lifting definition in lem-coef-kan-quillen-right-proper, the arbitrary-source-and-base clause of lem-coef-kan-realization-serre, the natural pullback homeomorphism in lem-coef-realization-finite-limits, and every path/action/exactness clause of lem-coef-serre-homotopy-exact-sequence; PASS after writing out the T_b horn filler. No Kan-base hypothesis is smuggled in; the empty-fiber argument uses path lifting, not a chosen point in an empty set.
- Step 2: checked against the weak-equivalence definition and the Serre node's orbit and stabilizer statements; PASS. The total component bijection restricts over each base component, equality of stabilizers follows from the total pi_1 isomorphism, and the explicit coset test supplies injectivity within each orbit. The empty source orbit set forces the target fiber empty.
- Step 3: checked both kernel and image chases against the Serre node's natural exact sequence; PASS. The first chase uses total pi_n injectivity and pi_(n+1) surjectivity; the second corrects on the left by the boundary class. Both apply for n=1 without assuming abelian groups.
- Step 4: checked against the Serre node's equivariance and orbit identification; PASS. The inverse of an equivariant bijection is equivariant, each realization component contains a vertex by the representing simplex, and empty orbit sets give no exception.
- Step 5: checked against the Serre node's exactness and naturality; PASS. The n=1 surjectivity argument uses only pointed-set exactness and injectivity on fiber components; the n>=2 case uses fiber groups. Ordered multiplication gives the required fundamental-group correction.
- Step 6: checked against the realization-based weak-equivalence definition and its cubical homotopy convention (in def-cbc-enhanced-diagrams-cones, named by the cited definition node); PASS. The collar construction and reversed path give mutually inverse basepoint-change maps and commute with postcomposition. This is an elementary construction from the definition. A simplex always has a vertex, so B_0 empty implies E=T empty.
- New nodes: none; B1-B10 and node-removal/leaf conversion checks are vacuous for children. The item is not a clause moved to a new node. The existing homotopy-fiber detection node requires all objects Kan; the two single-fibration criteria test contractible fibers and do not state this comparison of two fibrations over an arbitrary base.

Small cases checked independently: empty B; empty total spaces over nonempty B; empty E mapping into an occupied fiber of T (both conditions fail); B a point; disconnected B with missing fibers; identities; and product fibrations over Delta^1, a non-Kan base. There is no ring, scheme, or integer parameter in the item. No statement dispute was found. No Lean source or compiler was run, no SGA source was used, and the item statement and route were preserved.

Changes: replaced the phrase "the same argument" in step 1 with the actual lift through q and its factorization through T_b (E5); clarified that positive-dimensional horns have vertices, accounting for empty fibers. Added fresh second-reader leanfinder and grep searches with their actual logged results and source-checked no-match verdicts; Over.lean:88-105 and Bifibrant.lean:112-125 only inherit predicates, while Instances.lean:224-245 and Homotopy.lean:121-143 already assume a weak equivalence. All nine citations.json entries were independently checked verbatim against the shared statements and against the exact step/node pairs; the proof change introduces no new citation, so citations.json needs no rewrite. The original author's sections, including Review by Q56, remain intact.

Validation: the required deliver.py --no-push dry run printed OK at e3eee7aa50 on 2026-10-17; server preflight passed. Final delivery runs the same preflight before pushing.
