# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-pur-closed-etale-transport-bounds.json`: statement; split in five steps; no Mathlib match.
- `citations.json`: ten verbatim statement excerpts, one for each step/node use.
- `searches.jsonl`: seven searches made with the required msearch command; the previous imported search records in the item are retained and the newly executed results appended.

New nodes: 0. Mathlib leaves: 0. Neither the unit record nor any Lean file was changed. All writes were under this item's sandbox; no compiler or git command was run in the shared repository.

## Attachments

None. The exact blueprint-tag search of `lean/WeilConjectures/` was empty. Searches for closed-support, exceptional-functor transport, constructible intervals and Tor amplitude found constituent results, not a declaration giving every assertion under the item's hypotheses. In particular `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekMapDerivedCategoryObjIso` in `SixFunctors/ProEtale/FiniteCoefficient/Derived/UpperShriekPreservation.lean` gives the comparison isomorphism, not the two bounds. `exists_preservationClauses` concerns a chart/dimension-dependent bound, not the specified complement constant c. Those partial results do not justify ATTACH.

## WANTED

None. The current blueprint files and the relevant Stacks sources are present. No SGA source was used.

## What was wrong or missing

The item was unsplit, with an empty proof. Its statement is correct and was preserved verbatim, as were all eight statement dependencies and its original creation/blueprint metadata. No statement dispute was found. The important missing work was to expose the actual comparison map and distinguish the cohomological assertion, which requires no finite Tor amplitude, from the Tor assertion, whose pro-etale tests include sheaves not of etale origin.

The proof follows the closed-support part of Step 2 of the current `thm-pur-general-admissibility.proof.md`. The item is auxiliary to that statement, not the unit's key node. The unit's closed-support route is retained. General comparison results are declared as tool uses where they lie outside the unit; the ordinary etale amplitude and Tor results are precisely the two inputs named by the ancestor proof. No unit or chapter route was replaced.

The main-20261015 Tor-comparison proof is read for its intended two directions; the current DAG statement and repaired split of `lem-sf-comparison-tor-amplitude` supply the exact theorem used. In particular the present split does not repeat the old informal bounded-below argument for tensors that may be unbounded below.

## Not duplicates

No new node was created. Whole-DAG concept searches and whole-blueprint searches for closed etale transport, witnesses/intervals and closed-support computations were made before deciding to reuse the existing nodes. The general finite-ring constructible-origin theorem and both directions of the existing comparison Tor theorem already cover all proposed auxiliary comparison claims. Making separate witness, unit-identification, interval-transfer or Tor-transfer children would duplicate these results or merely restate clauses of this item.

## Review by NG

I read the item's current statement, its chapter record, its finite-exceptional-preservation unit, its blueprint ancestor and the current main-20261015 ancestor proof, especially Step 2. For the supporting sources I read Stacks `proetale.tex` Tag 09AK (`lemma-compare-constructible`), Tag 09AL (`lemma-compare-constructible-derived`), and Tag 099V (`lemma-relative-comparison`), together with the current blueprint proofs of `lem-exc-closed-amplitude`, `prop-exc-closed-tor` and `lem-sf-comparison-tor-amplitude`. There are no new-node sources to review. I opened and read the full statement of each node cited by the five steps rather than taking a fact from its proof.

Step 1 uses the existing finite-ring constructible-derived-origin statement. It explicitly gives an equivalence for arbitrary schemes and finite commutative rings and preserves and reflects each cohomological interval. The ring A here has exactly those properties. Thus the witness is bounded constructible and, in clause 1, lies in the requested interval. No qcqs condition or finite Tor hypothesis has been added.

Step 2 uses only the finite formula of the exceptional-inverse-image definition and the precise unit assertion of `thm-weil-pbc-site-comparison`. Its unit theorem applies on D+ without requiring constructibility or finite stalks; our witness is bounded, so it qualifies. I checked the direction of the unit, the application of Rnu to alpha, and the inverse of their composite. I wrote the equation on witness morphisms to justify naturality. This is a short functorial argument, not a new comparison theorem. I use no constructible-preservation claim embedded later in the exceptional-inverse-image definition.

Step 3 uses the two literal clauses of the complement-condition definition as the two hypotheses of the ordinary etale amplitude lemma. The latter's statement includes the constructible conclusion and the exact upper endpoint s+c+1. It does not require finite Tor amplitude. The same finite-ring origin theorem on Z preserves both constructibility and that interval. Step 2 then identifies its result with the functor specified in the item.

Step 4 uses clause (ii) of `lem-sf-comparison-tor-amplitude`. I verified the fixed finite coefficients, invertibility of ell on T, bounded constructibility of B, the given Tor interval and bounded-belowness of every witness. Its conclusion is the etale Tor predicate against every degree-zero etale module sheaf. The witness is arbitrary, so this proves the stated universal assertion about witnesses.

Step 5 uses `prop-exc-closed-tor` with its exact DVR quotient ring and both complement hypotheses; the complementary open is explicitly quasi-compact and c is nonnegative. It gives bounded constructible C_e with etale Tor interval [r,s+c+1]. Clause (i) of the comparison Tor theorem, now on Z, supplies the pro-etale interval with the all-module-sheaf quantifier. The endpoints remain ordered. Tensoring the Step 2 isomorphism with each test sheaf and taking cohomology is the explicit last argument; no assertion that arbitrary pro-etale test sheaves descend to the etale site is used.

I checked the B-to-E return checklist. There are no new-node shape, duplicate-tag or Mathlib-leaf-identification issues. Every non-elementary input is a cited existing theorem, with a verbatim excerpt in citations.json; no definition is substituted for a theorem. The union of the step uses is exactly proof_deps. The comparison children have no dependency path back to this item. No proof step exceeds 2000 characters (lengths 450, 676, 537, 595 and 801). No lemma is hidden inside a long step.

Small cases checked: B=0; r=s including negative degrees; c=0; i=id with empty complementary open; Z empty; n=1 and n>1 where A is nonregular and the two clauses cannot be conflated. In the identity case the widened bound contains the original one; on empty Z the output is zero. Clause 1 applies to non-flat constructible sheaves as intended. For clause 2 the test includes nonclassical pro-etale sheaves through the explicit quantifier of the existing comparison result. No counterexample or extra hypothesis was found.

Mathlib searches were run with leanfinder and loogle, grep and leansearch, including a second semantic phrasing. I read the returned declaration types; they concern etale morphisms, generic exact functors, sheaf pushforwards, topological constructibility and pro-etale-site definitions. I also read the Mathlib Proetale and ElladicCohomology files returned by grep. None supplies this exceptional closed-support bound or its site transport. All seven services completed successfully; none was recorded as unavailable.

## What remains unfinished

No part of this one-level split remains unfinished. Existing dependency nodes retain their own proof status. Server dry run and push follow this report; their exact outcome is recorded by the delivery tool.
