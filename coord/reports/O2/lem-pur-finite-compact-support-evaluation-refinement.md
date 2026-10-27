# O2 stage-1 report

## Files written

- dag/nodes/sec-six-functors/lem-pur-finite-compact-support-evaluation-refinement.json: statement, split; no Mathlib match. Six proof steps, no new nodes and no new Mathlib leaves.
- citations.json: thirteen verbatim statement quotations for every proof-step use.
- searches.jsonl: five searches actually run through msearch.py; the node retains its earlier searches and records these new results.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint id and for strict tower, evaluation, compact-support and refinement terminology. The hits on normalized adic towers and geometric compactification towers do not state the item. No finished project declaration giving its clauses was found.

## WANTED

None. The Stacks source files and newest blueprint proof are available locally. The strict-tower evaluation assembly is an agent argument using existing DAG lemmas, not a theorem attributed verbatim to Stacks.

## What needed repair

The node had a statement and empty proof. Its main traps are identifying an evaluated map only at the underived level, assuming evaluation faithful, and applying bounded-below finite-site comparison to an arbitrary unbounded input. The split keeps the statement unchanged, proves the evaluation assertions on all unbounded objects, and uses the witness hypothesis only for finite-site normalization and invertibility. Its compactifications are supplied: no extra Nagata existence hypothesis is introduced. The occurrence of def-exchange-projection in the statement refers to its ordered formula; that definition's coefficient/geometric setup is narrower than this item's setup, so the proof instead constructs the formula directly by the general mate and open-comparison nodes and does not import its narrower hypotheses.

The latest blueprint ancestor proof is the constituent-compatibility paragraph of prop-pur-weil-equivariance-compatibilities. I also read latest/sec-six-functors-basics/sk-prop-sf-cbc/fix-lem-exchanges.proof.md, especially Steps 1, 3 and 5. The package unit assembles base-change coherence from these constituents. No chapter or unit route is changed, and this auxiliary is not the unit's key statement.

## Unfinished

Nothing in this one-level split. The existing lemma dependencies remain the DAG's responsibility. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes. Whole-DAG searches for 0F7F, evaluation of units/counits and evaluated refinements, and blueprint_refs searches for evaluation, evaluation of, and common refinement found the existing tools used here. The item is an assembly of those tools; none of the blueprint hits states its complete unrestricted evaluation assertion together with its witnessed finite normalization.

## Review by O2

I read Stacks more-etale.tex, Tag 0F7F, label lemma-shriek-proper-and-open-base-change, including the K-injective construction and its normalization diagram. It proves the etale compatibility, not the strict-tower claim. I read sites-cohomology.tex, Tag 07A7, remark-base-change, whose exchange is the transpose of the square comparison followed by the derived counit, and its composition discussion. The proof_origin is agent because deriving finite evaluation and common-refinement transport from the existing tools is additional assembly. There are no new nodes requiring separate sources.

Step 1 uses the statement of lem-cbc-tower-mate-evaluation-scalars, which explicitly gives the K-injective evaluation comparison and preserves derived units, counits and transposes on arbitrary unbounded objects. It does not use merely an underived comparison or scalar restriction preserving K-injectives. The statement of lem-sfb-derived-composition-adjunction-normalization identifies the resolution compositor with the derived adjoint conjugate, including its units and counits. The module and tower categories meet its Grothendieck hypotheses in the setup of the first cited lemma; the inverse images are exact. This checks the compositor needed when the refinement map is pushed down.

Step 2 uses the actual unit-square-counit formula of def-weil-pbc-adjunction-mate and the statement of lem-cbc-tower-open-beta-normalization, which specifies finite evaluation of beta. I expanded the three proper-mate factors so that matching units and counits proves equality of the specified maps. The arbitrary base change is allowed by the open normalization, and the proper square only needs supplied proper maps. The final multiplication is functoriality, not a new comparison theorem.

Step 3 checks Q_u itself: its left map is identity, its right map is the supplied proper refinement, and its two open maps are quasi-compact. The statement of lem-cbc-strict-tower-proper-open-calculus specifies its clopen-section projector; lem-cbc-tower-mate-evaluation-scalars then explicitly evaluates the projector's proper mate. The item defines the ordinary comparison by precisely that formula. Applying the direct-image comparison of Step 1 supplies C_u, with its direction F_2 to F_1. This step uses the statements, not any unstated construction from their proofs.

Step 4 uses lem-cbc-finite-clopen-mate-site-transport for exactly the witnessed bounded-below finite object and the refinement square. Its statement says the mate is the normalized finite etale comparison and an isomorphism. For exchange normalization, lem-weil-pbc-transport-identifies-exchange requires qcqs verticals: the two compactification proper maps satisfy this, regardless of whether the base itself is qcqs. Open extension is exact, so the etale input j_!L is still bounded below. Combining its explicit identification of the proper exchange with the open beta normalization gives the same ordered finite compactification formula. thm-cbc-finite-level-proetale identifies that transported formula with the specified pro-etale exchange, with no constructibility or characteristic restriction. The witness is conjugated as that statement requires. No site-comparison claim is made for an unwitnessed object.

Step 5 uses the levelwise kernels/cokernels statement of lem-weil-tower-category-levelwise-abelian to define the exact constant-tower functor. For a witnessed N, the hypotheses of lem-cbc-complete-proetale-refinement-exchange-coherence hold with B=Lambda and all coefficient homomorphisms identities; N occurs at every level with its own bounded-below witness. Its displayed identities are actual equalities in the tower derived category. Applying evaluation and Steps 1-3 proves the finite identities. For nonconstant original M this is done independently at each N=ev_n M, so neither a uniform bound nor faithfulness of derived evaluation is needed.

Step 6 uses precisely the common-refinement and parallel-arrow-equalizer clauses of lem-cbc-compactifiable-cofiltered, whose statement explicitly permits arbitrary bases with supplied compactifications. I wrote the cancellation under further refinement, the common-three-object cocycle, and the equation intertwining exchanges. The last conjugation argument is substitution of isomorphisms in an equality; its intermediate inverse pairs cancel. The final reference to fix-lem-exchanges identifies the restricted domain and chosen map via Step 4; it is not a proof dependency on fix-lem-exchanges' coherence conclusions. Thus there is no circular invocation of the conclusion being normalized.

I checked delivery-errors B-E throughout. No statement-only nodes were padded with proof, no new elementary or duplicate lemmas were introduced, and every non-elementary input is in a step's uses. Each of those thirteen uses has an exact statement quotation in citations.json. The union of uses equals proof_deps. Every proof step is below 2000 characters; none hides a new independently asserted comparison. The off-unit generic tools are declared in split_report.tool_uses for maintainer review, not in the maintainer-owned tool_uses field.

Edge cases checked: zero ring and zero complex give the same zero maps; identity refinement yields the identity under the normalized compositors; identity base change gives the canonical identity; empty X gives the zero compact-support functors. Arbitrary non-qcqs bases are allowed because compactifications and the cofilteredness theorem are supplied, not inferred from Nagata. An arbitrary unbounded tower need not have witnesses: Steps 1-3 still apply but Step 4 onward is restricted as in the statement. Bounded-below witnesses may vary with n. No extra etale lift of the tower transitions is required; constant towers in Step 5 already carry their identity transitions.

Mathlib results were read: evaluationAdjunctionRight and evaluationAdjunctionLeft in CategoryTheory/Adjunction/Evaluation.lean describe underived functor-category adjoints; SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app and its counit analogue at PushforwardContinuous.lean:298,303 concern underived sheaf adjunction components. LeanSearch's limitObjIsoLimitCompEvaluation_inv_π_app is ordinary limits in a functor category; the other semantic hits concern inverse-system sets, condensed solid modules, or unrelated local cohomology. None states this derived proper/open compact-support normalization or specializes to it in one line. Both semantic phrasings, Loogle, LeanSearch and the source grep are recorded as actually run.
