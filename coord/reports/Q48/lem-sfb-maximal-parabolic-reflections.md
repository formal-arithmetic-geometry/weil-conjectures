# Worker report: lem-sfb-maximal-parabolic-reflections

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-maximal-parabolic-reflections.json — statement item, now split into five proof steps; not a Mathlib leaf.
- citations.json — twelve verbatim statement quotations, one for each step/node citation.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0. The item statement and its statement dependencies are unchanged. No Lean, library, unit, chapter, launcher or repository file was written. Scratch text and a JSON-writing script are confined to this item's sandbox.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, parabolic, Borel, Bruhat, cocharacter and simple-reflection notions found no declaration stating the item. The broader lean/Sheaf search found only other group-theoretic prerequisites and unrelated generic-initial-Borel material.

## WANTED

None. The source is available locally: Milne, Algebraic Groups (iAG2017), Proposition 21.88 and proof, printed page 452, with the application in Lemma 22.24, page 469. No SGA source is used. This algebraic-group proposition has a Milne source rather than a Stacks tag; no tag is invented for it.

## Corrections and observations

There is no statement dispute. The imported source informally uses a rational fundamental cocharacter inside P(lambda). I explicitly multiply it by a positive integer to obtain a genuine cocharacter before applying the limit-subgroup theorem. This imposes neither simple connectedness nor a restriction on characteristic. Strictness is shown by the negative root tangent weight, an immediate application of the existing limit-subgroup tangent-space formula, rather than leaving the source's noncontainment argument implicit.

The nearest-ancestor command prints `a node created for lem-sfb-maximal-parabolic-reflections has blueprint.from.node = None`. Following created.item reaches lem-sfb-admissible-direct-image and then the Lean module name Sheaf.SixFunctors.CtfStabilityDirectImages, not an imported blueprint node. I retain the inherited null from.node, its full precise from.place, and its via chain; I do not manufacture an ancestor. The current latest blueprint det-thm-sf-ctf-stability-direct-images proof (3) was read, as were the chapter and unit records and the latest unit text. The split stays in the existing alteration/representation-theory prerequisite chain below that direct-image route. No chapter or unit route is replaced.

## Mathlib and duplicate searches

I retained the item's four inherited search records. The actual fresh msearch.py calls and their results are logged in searches.jsonl: LeanFinder with a subgroup/Borel/reflection formulation; Loogle `"parabolic"`; grep `parabolic|Parabolic|BorelSubgroup`; LeanSearch with the distinct fundamental-cocharacter/limit-subgroup formulation. All services answered. The hits concern abstract Coxeter/Weyl groups, Lie algebras or the discriminant-zero meaning of a parabolic matrix. I read Matrix.IsParabolic at Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean:40, RootPairing.weylGroup at Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean:56, and CoxeterSystem.subgroup_closure_range_simple at Mathlib/GroupTheory/Coxeter/Basic.lean:241. These do not give a smooth closed group subscheme with the claimed containments.

Whole-DAG searches for parabolic subgroup, cocharacter centralizers, 21.88, Borel/root-product geometry and rational simple-root spans located the existing nodes used below. Whole-blueprint searches with blueprint_refs.py for parabolic, cocharacter and simple reflection gave zero matches. No new node is proposed: in particular neither the clauses of this item nor the elementary denominator-clearing and reflection calculations were relabelled as new nodes.

## Review by Q48

I read Milne 21.88, including its formula (138) and the full reflection calculation, and the opening proof of 22.24 to verify the intended use. I also read Theorem 13.33(a)--(e) on printed pages 265--266, Theorem 21.11(b)--(e) on pages 428--429, Theorem 21.68(a),(b) on page 445, and the semisimple lattice discussion 22.9 on page 465. There are no new-node sources to audit. Every existing node cited below was opened and its actual statement checked; citations.json contains the verbatim parts used, not a paraphrase or a quotation of its proof.

Step 1 uses the Borel-pair statement for semisimple implies reductive, the integer perfect pairing and the positive-root base. The semisimple-roots-span statement gives rational spanning in precisely the semisimple hypothesis here. The root-base-rational-integral-spans statement then gives the rational simple-root basis; its hypotheses are the reduced crystallographic rational root system supplied by those two nodes and the simple-root base already in force. The dual basis and the common denominator are finite rational linear algebra: after choosing split-torus coordinates they produce an integer cocharacter, not merely a rational one. Positive-root coefficients give the nonnegative weights by an explicit sum.

Step 2 uses only the cocharacter-limit-smooth-structure statement, which explicitly represents P_lambda by a smooth connected closed subgroup and gives its functor on all test algebras. Its hypotheses hold because G is smooth connected affine of finite type and lambda is an actual group-scheme cocharacter after step 1. No assertion about existence of a smooth subgroup is inferred just from geometric points.

Step 3 uses the root-subgroup-parametrizations statement for the conjugation formula on every commutative algebra, the limit-subgroup statement for the extension criterion, the Borel-root-product-coordinates statement for the isomorphism of the positive-root product with U, and the Borel-pair statement for B=U semidirect T. The displayed nonnegative power formula extends to A[t] for every A, so the claimed inclusions are subgroup-scheme inclusions. No rational-point density or nonreduced-subscheme inference is hidden here.

Step 4 uses the rank-one-reflections statement for the existence and nonzero one-dimensional space of -alpha_i, and the limit-subgroup statement for its direct weight decomposition and exact tangent subspace formula. The weight is -d as an integer character, so it remains negative even when the characteristic divides d. Equal subgroup schemes have equal tangent spaces, giving the required strict inclusion. This is strictness of a subgroup and makes no assertion that its inclusion morphism is nonproper.

Step 5 uses the rank-one-reflections statement for the pairing-preserving actions of the actual normalizer quotient and the character reflection formula. Squaring that formula gives involutivity; duality and the zero pairing with alpha_j give s_j lambda=lambda. This means equality of cocharacter morphisms, hence the orbit of any representing n is constant. The limit-subgroup statement then puts n in P_i(F). This is a direct calculation from the cited statements, marked elementary, and it treats all representatives, not a selected one.

Small cases checked: rank zero has no index i. In rank one, including SL2 and PGL2, the denominator-cleared lambda defines the Borel and the assertion about other reflections is empty; this also tests the absence of a simple-connectedness assumption. For SL3 with its diagonal torus, a multiple of the first fundamental cocharacter has exponents (2,-1,-1), so the second simple reflection centralizes it while the first negative-root weight is strictly negative; the roles interchange for the other index. Product root systems give zero pairings on the other factors and cause no change. In characteristic 2 or 3 the proof uses scheme characters and the full root subgroups, so differential collapse is irrelevant.

Against delivery-errors B--E I checked self-contained unchanged statement, unchanged definition dependencies, real (recorded) searches, exact statement citations with hypotheses, no circular dependency back to the item, no missing non-elementary input, and no duplicate or clause-restatement nodes. The used existing nodes all have the item's unit sk-thm-sf-ctf-stability; there is no off-unit tool use to declare. Each proof step is below 2000 characters. No mathematical work remains unfinished; server dry run and delivery are recorded below when complete.

## Not duplicates

No new nodes; no new/existing same-tag pairs.

## Server validation

The required deliver.py --no-push process exited 0 with `OK (not pushed)` at 66aa5219708 on 2026-10-24. The server's stage-1 preflight, including check_dag and review_split, passed. No checker or compiler was run locally.
