# Stage-1 delivery: lem-sf-open-reduction-adjunction-transport

Group NO; 2026-10-21; direct delivery.

## Files written

- dag/nodes/sec-six-functors/lem-sf-open-reduction-adjunction-transport.json: statement, split into eight proof steps; no exact Mathlib match.
- citations.json: fourteen verbatim statement quotations, one for every node cited in every step.
- report.md: this report. searches.jsonl contains the searches actually run; write_split.py is a sandbox-only JSON preparation script.

No new nodes and no new Mathlib leaves. The item statement, its statement dependencies and its source are unchanged. No unit record is changed: this item is not the unit's key node.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag and open/reduction/adjunction notions did not find the item. I read the derived open-immersion adjunction in SixFunctors/ProEtale/ModuleObject/Derived/OpenImmersionLowerShriek.lean. It gives the module-object adjunction, but not this item's strict varying-coefficient reduction comparisons, actual-unit realization or displayed equations. It is not an attachment for the item.

## WANTED

None. The needed source texts are available.

## Changes and discrepancies

The imported item was unsplit, with no proof. The split retains all its hypotheses and conclusions. In particular it does not derive actual-unit invertibility from the triangulated completeness definition: that invertibility is an explicit hypothesis. Preservation of completeness by extension by zero is also a hypothesis; no quasi-compactness of the open immersion is introduced. Ordinary restriction and its actual completed comparison come from the existing immersion theorem.

The strict tensor representative is already stated by lem-sf-open-semilinear-tensor-model. I cite it instead of creating another node or reproving its flatness and resolution-independence clauses. The item itself carries the unit and counit computations and the subsequent formal calculations; no clause was moved into a new node.

The Stacks sources give the open tensor formula and total-limit foundations, not the full semilinear adjunction-transport assertion. Accordingly proof_origin.by is agent, and the step sources distinguish the tags from the additional existing agent-formulated system tools. No prohibited SGA source is used.

Nothing remains unfinished within this one-level split. The existing cited unsplit tensor-model node remains a separate item, as required by the stage-1 contract.

## Searches and reuse

There was no earlier sandbox node, split, report or search log on first inspection. I read the repository's previously recorded Mathlib searches and reran all five recorded query texts through msearch.py. Both LeanFinder phrasings, Loogle, LeanSearch and grep completed successfully. The hits concern generic derived or restricted adjunctions, module-sheaf adjunctions, ringed-space restriction and condensed objects, and do not state this item's simultaneous reduction/completion comparisons. A further msearch grep located CategoryTheory.Adjunction.derivedε at Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:118. I read lines 95–155 there, including derivedη_fac_app and derivedε_fac_app, and the unit/counit formulas in CategoryTheory/Adjunction/Restrict.lean. These generic theorems do not supply the strict coefficient-system or quotient-completion hypotheses and constructions, so the item is not a one-line Mathlib specialization.

I ran blueprint_refs.py ancestor and whole-blueprint searches for adjunction, completion unit, open tensor and open restriction, and searched the DAG by these notions and the source tags 0GL1/0E8I. The ancestor is fix-prop-coherence. No blueprint node states this entire actual-completion-unit assertion. The existing tensor-model node supplies a strictly smaller ingredient. The blueprint reference remains its precise existing integral-open-factor place, with same_as empty. The main-20261015 fix-prop-coherence text was read, together with the live chapter and unit records. This is the coefficient-compatibility route of sk-thm-sf-compatibility clause (7); there is no reroute.

## Not duplicates

No new nodes. The tensor-model, immersion-comparison and system-calculus nodes are reused directly. The formal naturality and triangle-identity calculations are proof steps, not new category-theory lemmas.

## Review by NO

I read delivery-errors B–E in full and checked the split against each listed class of error. For the item I read Stacks sites-modules.tex, Tag 0E8I, label lemma-j-shriek-and-tensor (around line 4051), including its adjunction calculation, and sites-cohomology.tex, Tag 0GL1, the same label (around line 4578), including its K-flat proof. I also read Tag 0941, label lemma-derived-limit-is-ok (around line 5067). These sources justify the tensor and limit foundations only; the report and proof do not attribute the new system equations to those tags. There are no new node sources to audit.

For Step 1 I opened and read the statement of lem-sf-open-semilinear-tensor-model. It explicitly supplies flat-term K-flat preservation, the generator formula for r_Q, all quotient and scalar-unit squares, naturality, localization and resolution independence. Its hypotheses allow the arbitrary open immersion of the item, without completeness or quasi-compactness. This is precisely the ingredient used, rather than the proof of that node or the stronger parent item.

For Step 2 I opened all four cited statements. The immersion-comparison node explicitly gives exactness, preservation of quotient completeness, and the actual ordinary-to-completed comparison with completion and finite projections. An open immersion qualifies as a locally closed immersion by taking the identity closed factor. The coefficient sheaves and canonical identifications agree exactly with those of the item. The ringed-topos tensor-pullback node explicitly preserves flat-term K-flat complexes. The reduction calculus explicitly computes all reductions using one such representative, and the semilinear-sections node supplies simultaneous scalar extension and localization. The text writes the strict restriction/tensor map and its quotient and augmentation squares, rather than invoking equality detection by evaluation.

For Step 3 the open-tensor-normalization statement gives the identity-section normalization of the actual open unit, and the semilinear statement gives the actual termwise open adjunction and simultaneous derived units/transposes. For Step 4 the K-flat pullback statement and the tensor-model statement let restriction and extension of the same representative compute both sides. The semilinear statement again supplies the actual system counit. I checked the argument on each extension-presheaf summand: the two counit words both send [x] tensor a to x tensor a. This equality precedes sheafification and localization, and every quotient transition is the same coefficient reduction on a. These are elementary explicit map calculations using the cited constructions, not assumptions that evaluations detect equality of derived morphisms.

For Steps 5–8 I read the actual reduction/limit adjunction paragraph in lem-coef-derived-system-evaluation-calculus; it states the actual unit, counit and system-category triangle identities. Step 5 checks the necessary completeness hypotheses separately before inverting u. Step 6 uses e_(R A) composed with R(u_A) = 1 and naturality of e for r; its equation has source R L(J R K) and target J R K. Step 7 rearranges the reduced unit identity, then applies naturality of u to eta^o_K. Step 8 expands the inverse of d and uses the reduced counit identity, then naturality of u for epsilon^o_H. I checked all sources, targets and inverse directions. In particular d_(j^*H)^(-1) is L(r_(j^*H)) composed with u_(j_!j^*H), which is the direction needed in Step 8. These are written calculations, so no additional non-elementary transport lemma is hidden in them.

The proof has no step longer than 2000 characters. It creates no unsplit definitions, no new statements, no Mathlib leaves requiring a questionable equivalence of notions, and no replacement node restating a clause. Every proof citation has a verbatim statement quotation in citations.json. Off-unit generic tools are declared in split_report.tool_uses, with their specific purpose; no maintainer-owned tool_uses field is set.

I checked the small cases U empty, U = X and K or H zero. For U = X the strict comparisons are the canonical identities and d,b reduce to inverse actual completion units; Step 6 is exactly the triangle identity. For U empty and zero complexes the maps and equations are the unique zero maps on the relevant zero objects. The generator calculations also apply to a sheaf in degree zero and to every quotient transition m to n, without requiring quotient maps to be flat. No statement dispute or missing hypothesis was found. No repository, launcher, Lean source or build artifact was written.
