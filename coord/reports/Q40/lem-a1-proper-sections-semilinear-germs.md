# Q40: lem-a1-proper-sections-semilinear-germs

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-proper-sections-semilinear-germs.json`: statement, split into eight proof steps; no Mathlib match for the complete statement. Statement retained verbatim. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every dependency of every proof step.
- `report.md`: this report. Sandbox-only scripts `write_split.py` and `finish_split.py` prepared the JSON; `searches.jsonl` is the search command's own log. No Lean, compiler, git command, live file or launcher file was changed or run by the worker.

## Attachments

None. I searched the whole project `WeilConjectures/` for the exact blueprint tag and the semilinear/germ concepts, and inspected `WeilSheaf/StalkFrobenius.lean` and the adic geometric-Frobenius implementation. The proved `globalSectionsToStalkObj_*` identities there concern ordinary sheaves with Weil structure, not arbitrary objects of the completed/rational/common-stage derived categories in this item. In particular `AlgebraicGeometry.WeilSheaf.globalSectionsToStalkObj_frobenius` assumes Weil structure and a fixed-point condition and proves a degree-zero formula. It does not attach this item.

## WANTED

None. Deligne Weil II, the current blueprint, the Stacks sources and Mathlib source used here are locally available.

## Corrections and choices

The item statement needs no correction. Its source explicitly calls this an agent refinement; Deligne does not state the displayed derived identity. The proof is therefore marked agent-written. I read Deligne (1.1.3), (1.1.7), (1.1.10)--(1.1.14), printed pp. 150--153 (PDF pp. 15--18), Stacks 07A7 (`sites-cohomology.tex`, `remark-base-change`) and 0D6D (`lemma-derived-pullback-composition`), and 099N (`proetale.tex`, `lemma-pushforward-Noetherian-case`, especially (2), (5)). These provide the transport convention, the counit-defined exchange and the completed pullback convention. The proof below those interfaces is explicitly supplied in the item's steps.

I retained the exact exchange and point transport throughout. Replacing point transport by an arbitrary identification would not prove the item. I did not infer equality of integral morphisms from their finite reductions: step 3 applies a functor to a single identity of actual derived-system maps. I did not reduce rational objects modulo a uniformizer, assume a Weil structure, assume finite Tor dimension, or treat semilinear Frobenius as a morphism over k.

I read the chapter and unit records and the current ancestor blueprint proof. The ancestor's Galois-invariants evaluation formula has already been repaired upstream of this child; this split only supplies the semilinear evaluation compatibility and does not use that false formula. The unit's evaluation/weight route is preserved. Seven generic existing tools outside this unit are declared individually in `split_report.tool_uses`; they supply proper comparison, adjunction, coherent pullbacks, coefficient passage, point-transport naturality, strict-system adjunctions and the derived-limit functor. The generic mate-counit result is already a Mathlib leaf, so needs no off-unit declaration.

## Not duplicates

No new nodes. The whole-DAG/blueprint searches included counit, transport, semilinear germs and derived global germ. I reused the existing exact general fact `lem-amb-mate-unit-counit`, whose `CategoryTheory.mateEquiv_counit` proof is at Mathlib/CategoryTheory/Adjunction/Mates.lean:123. The topological-stalk, scheme residue-field evaluation, finite-coefficient graph exchange and degree-zero Frobenius lemmas do not state this derived completed/rational identity. Since the remaining calculations are short substitutions from the cited statements, they are steps, not extra nodes.

## Unfinished work

None in the assigned stage-1 split. No statement-only subproblem was introduced. This is not a claim that the existing dependencies are all Lean-proved.

## Review by Q40

I checked the split against delivery-errors B--E with the actual cited statements open. There are no new statements requiring a separate source or a small-case test, and no new names duplicating a blueprint node. The imported statement and its blueprint ancestry are retained; all appended searches really ran using msearch.py, and their hits were read. Two semantic phrasings returned structure-sheaf evaluation or slice-category evaluation results, not this item; the Loogle query found the general mate lemma already in the DAG. The relevant source declarations were read, including the distinction between residue-field evaluation and constructible coefficient complexes.

For step 1, I checked that `lem-pod-proper-coincidence-frobenius` expressly states the natural identity-compactification comparison and its compatibility with tau, for integral as well as rational coefficients. This is exactly what permits conjugating the formula to ordinary cohomology. `def-weil-frobenius-cohomology-transport` expressly defines the ordinary transport as point transport followed by the exchange, and supplies naturality. Properness and use of the same identity compactification are hypotheses of the item.

For step 2, `fix-prop-adjunctions` gives the ordinary completed adjunction and its counit for the structure morphism. The item already fixes the germ using that counit. `lem-pod-integral-pullback-composition` gives the natural comparison used for a_Y x = id and its associativity. I wrote v_x = x*(epsilon) u_x^{-1}, so its source is R M and its target x* M in the same derived category on s; naturality is the counit's naturality square. The vertical maps used here are over k, whereas the semilinear maps are only used as scheme maps for pullback.

For step 3, I verified the substitution L_1 = L_2 = A, R_1 = R_2 = R, G = Q, H = P in `lem-amb-mate-unit-counit`: its conclusion is precisely epsilon_PM A(E_M) = P(epsilon_M) theta_RM. The exchange definition specifies that very system mate, not just an unspecified base-change isomorphism. `lem-coef-semilinear-derived-sections` supplies actual system adjunctions/mate words; `prop-weil-pbc-rlim-functoriality` supplies a genuine functor. `lem-fix-operation-reduction` expressly includes preservation of units/counits and exchange comparisons, so applying that functor and those comparisons gives the completed counit identity. I added both system/functor citations on re-reading this step, to avoid leaving the integral equality implicit.

For step 4, I checked both sides of the comparison identity have source QN and target x* P A N. The b indexed by A N is Q x_1* A N -> x* P A N, so it can follow Q(u_{x_1}^{-1}). Expanding either side amounts to the same reassociation using gx = x_1 h and a_Y x = a_Y x_1 = id. The cited associativity formula supplies exactly that reassociation. Naturality of b with respect to epsilon_M then gives the three displayed composites, all with source Q R M and target x* P M. This is the actual two-line calculation; it does not appeal to an unstated geometric-germ theorem.

For step 5, I verified that `lem-weil-frobenius-point-transport-natural` (2) quantifies over all derived morphisms, not merely degree-zero sheaf maps, and includes integral coefficients. Thus it applies to v_{x_1}: R M -> x_1* M. Its stated formula has exactly the orientation needed. `def-weil-frobenius-point-transport` specifies the iota in the resulting formula and its scalar passage. The proof does not substitute an abstract fiber equivalence for that arrow.

For step 6, I checked the induction has a base, the same claim at r and the step at r+1. At the step, the old formula is applied at x_1 and the one-step formula at x to P^r M. Naturality of iota is used on the actual b-hat morphism J_r x_{r+1}* M -> x_1* P^r M. It gives Q of that morphism on the left of iota, exactly the recursive b-hat. The successive point transports occur in the prescribed order.

For step 7, I checked the contracted comparison identity has source J_r x_r* M and target x* P_r M. It follows by expanding the adjacent squares and applying the already cited associativity formula, repeatedly. Germ naturality with d_r^{-1} then moves the final cohomology comparison to the fiber, and f_r^{-1} contracts the raw point transports. These are the d_r and b_r fixed in the item, so the induction proves the specified r-th-iterate formula.

For step 8, I verified that `def-weil-rationalization-karoubi` explicitly uses raw scalar localization with the same objects and localized Hom groups, and that `def-weil-algebraically-closed-coefficients` represents maps and compositions at a common finite stage. `lem-fix-operation-reduction` supplies the compatible coefficient passage; the point-fiber and point-transport definitions explicitly tensor at E and use finite stages at Qlb. Point-transport naturality includes those coefficient extensions. Hence every factor in the integral identity is the required factor after passage, and naturality extends to localized arrows and common-stage arrows.

I tested the formula on Y_0 = Spec(k_0), where all spatial germs are identity and the formula reduces to its very definition of iterated point transport; on a degree-two finite point, where T exchanges the two geometric components and the formula sends evaluation at z to evaluation at T^r z in the displayed direction; on the zero complex and shifted complexes, where no degree-zero shortcut is available; and on arbitrary r with r = 1 as the explicit base. For empty Y the assertion over points is vacuous. Nilpotents and nontrivial extensions of sheaves do not enter any formal substitution. No new hypothesis is needed. All eight steps are shorter than 2000 characters; none hides an additional geometric lemma. The non-elementary inputs are existing cited nodes, and citations.json contains literal excerpts from their statements for each use.
