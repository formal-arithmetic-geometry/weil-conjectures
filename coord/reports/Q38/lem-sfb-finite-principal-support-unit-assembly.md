# Stage-1 report: lem-sfb-finite-principal-support-unit-assembly

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-principal-support-unit-assembly.json: statement, now split in six steps; no exact Mathlib match.
- citations.json: 11 verbatim statement quotations for the 11 step-node citations.
- report.md: this report. No new nodes; no new Mathlib leaves. Only sandbox files were written.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for principal support, support/unit and localization-triangle terminology, including the internal module-object directory. The hits concern finite coefficients, ordinary scheme modules, or different supported-open assertions. No declaration states all clauses for arbitrary condensed coefficients and ordinary unbounded internal-module derived categories. No Lean was written or compiled.

## WANTED

None for this formal assembly: the existing all-coefficient support triangle and the existing derived pullback composition proposition provide its non-elementary inputs. This does not discharge the geometric supported-vanishing input of the parent root-tower lemma.

## What changed and what was wrong

The item was an unsplit statement with an empty proof. Its statement, hypotheses and source were retained unchanged. Six steps supply exact restriction, the single-complement actual-unit isomorphism, the conjugate-comparison unit equation, the normalized empty-set unit, finite-subset induction and ordering independence. No new fact is hidden behind a new restatement of a clause. The current ancestor command reports blueprint.from.node = None; I retained that existing provenance rather than inventing an imported ancestor. The recorded from.place identifies paragraph (3) of the current direct-image blueprint and the parent puncture-invariance calculation. Searches of the whole imported blueprint for localization triangle, adjunction unit, principal and support vanishing gave no duplicate of this complete assembly. The actual current parent proof, step 3, requests exactly this formal assembly after its separate supported-vanishing input.

## Not duplicates

No new nodes. Reused det-lem-formal-closed-support-adjunction, det-prop-sfb-module-pullback-exact-main, prop-sfb-module-left-derived-upper-star-comp, the conjugate and composite adjunction definitions, and the Mathlib zero-cone criterion. A finite-support-vanishing lemma duplicating the item or one of its clauses was deliberately not created.

## Review by Q38

I read AGENTS.md, the worker brief and role, stage 1, GOAL.md, the three SETUP levels, the chapter and unit records and delivery-errors B through E. The assigned item belongs to sk-thm-sf-ctf-stability but is not its key statement, so there is no unit realization edit. I read the current direct-image blueprint paragraph (3) and the parent root-tower-puncture-invariance proof: the geometric root-coordinate vanishing is separate, and the task here is only its formal finite-open assembly. This preserves the route and makes no SGA citation.

For step 1 I opened det-prop-sfb-module-pullback-exact-main and its current blueprint source: it states exactness for every commutative condensed ring and every scheme morphism. I opened sk-def-sfb-derived-categories and sk-def-sfb-module-derived-pushpull: the former identifies an exact functor with its total derived functor, and the latter supplies the specified derived adjunction for the full internal-module composites. These statements justify using restriction rather than silently changing coefficient categories or assuming boundedness.

For step 2 I read the entire statement of det-lem-formal-closed-support-adjunction and its source sk-lem-formal-closed-support-adjunction.md in the current blueprint. Clause (4) is precisely the distinguished triangle whose second arrow is the actual open unit; it is on ordinary unbounded categories for any condensed ring. Its quasi-compactness hypothesis holds because each complement is principal on the affine X_J (and remains principal over every affine open). The assumed supported object is zero, so its additive closed pushforward is zero. I read the rotation axiom in def-weil-triangulated-category and the exact statement of lem-kun-distinguished-cone-zero, then Stacks derived.tex Tag 05QR, label lemma-third-object-zero, and the corresponding Mathlib lines 372–391. Rotation is necessary: the cited criterion concerns the third object, whereas the unrotated support triangle has zero first object. This correction is explicit in the step.

For step 3 I read prop-sfb-module-left-derived-upper-star-comp and its current blueprint statement: it gives the canonical derived pullback composition for arbitrary schemes and arbitrary commutative condensed coefficients, induced by the underived comparison. I read def-weil-pbc-adjunction-conjugate and def-weil-pbc-composite-adjunction in full, Stacks sites-cohomology.tex Tag 0D6E (lemma-derived-pushforward-composition) and categories.tex Tag 0DV0 (lemma-compose-counits), and Mathlib Adjunction/Mates.lean lines 275–307. The Stacks proof uses uniqueness of adjoints; it does not alone assert the requested map equation. The step therefore spells out the conjugate-unit equation and substitutes the composite unit. The comparison is exactly the one specified by the item. A separate theorem identifying some other pushforward comparison is unnecessary because the item itself defines the comparison by conjugation.

For step 4 the same two definition statements give the identity adjunction and the conjugate of the canonical identity comparison. The unit equation already calculated in step 3 forces the normalized empty-set unit to be identity; it is not assumed that an arbitrary adjunction on identity-isomorphic functors has identity unit. Step 5 is elementary strong finite-cardinality induction using the previously proved steps: remove an element, use the hypothesis for that precise smaller subset, and apply a functor to an inverse. Step 6 substitutes the same map equation along each finite list, so every ordering gives the fixed eta_J. These last steps need no independent lemma or extra citation. Every step is under 2000 characters.

I checked the degenerate cases: r=0, K=0, empty X, empty intermediate opens, empty closed complements, f_a a unit, f_a=0 and nilpotent f_a. If a principal open is empty, the hypothesis forces K_J=0 by the same triangle; no false invertibility statement is inferred for a nonzero object mapping to zero. With a unit parameter the complement is empty and the triangle gives the identity-open case. There is no regularity, non-zero-divisor, characteristic, finite-type, constructibility or finite-Tor hypothesis used. The statement stays unchanged.

All step citations were generated from the actual existing statements and reviewed against their use, and proof_deps is their union. Generic off-unit support, exactness and derived pullback-composition inputs are declared in split_report.tool_uses. Mathlib search commands were actually run under Q38 for this item and their results were read: the two LeanFinder phrasings, Loogle and grep had no whole-item match; LeanSearch returned general derived-adjunction identities. searches.jsonl retains the exact queries and responses, including the second LeanFinder call that finished during the provider interruption. Earlier inherited Q61 searches remain untouched. No report claims an unavailable service returned no match.

## Unfinished work

None in the split. The dependencies remain their own DAG items; their proofs are not asserted to be closed here. Delivery still requires the server dry run and push.
