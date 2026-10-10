1. Files written:
   - `dag/nodes/sec-curve-estimates/def-sc-ringed-space-module-cohomology.json`: definition, no new child nodes, Mathlib searches found only general sheaf-cohomology primitives and no exact match.
   - `citations.json`: empty because the definition has no proof steps.

2. Attachments: none.

3. WANTED: none.

4. What was checked:
   - I read the item and its parent route in `dag/nodes/sec-curve-estimates/def-sc-ringed-space-module-cohomology.json`, the unit `sk-thm-curveestimate`, and the worker brief/checklist.
   - I searched the whole Lean source for the item id, its blueprint tag, and ringed-space/module cohomology declarations. No sorry-free project declaration states this definition exactly.
   - The statement agrees with the Stacks Cohomology Section 20.11, Tag 01DZ ringed-space module paragraph, and its use in the Mayer–Vietoris paragraph of Tag 09MR: an O_X-module is resolved by injectives in `Mod(O_X)`, and H^p is the cohomology of global sections of that resolution, independent of the choice and representing the right derived functors of Gamma.
   - The existing `lem-sc-ringed-space-module-sheaves-enough-injectives` node says precisely that the module category is abelian with enough injectives, which is the only nontrivial statement dependency needed to form the chosen resolution. Definitions of ringed spaces, O_X-modules, left exact/additive functors, and injective resolutions are already listed in `stmt_deps`.
   - I searched Mathlib with LeanFinder, Loogle, and grep using the required commands. LeanFinder returned `CategoryTheory.Sheaf.H`, `cohomologyPresheaf`, and `SheafOfModules.sections` primitives; Loogle reported an unknown identifier for the natural-language query; grep found no matching arbitrary ringed-space declaration. None states this exact definition, so no Mathlib leaf or new node was created.
   - As a definition, there are no proof steps; therefore `proof`, `proof_deps`, and `citations.json` are empty. The item is marked `split` with its blueprint `from.place` filled and `same_as` left empty after the blueprint search.

5. What could not be finished: nothing.

## Review by E1
I checked the item source and the 09MR/01DZ route, then verified each hypothesis in the statement: X with its sheaf of rings, F as an O_X-module, and an injective resolution in the abelian module category with enough injectives supplied by the cited node. Since this is a definition, its resolution-independence and derived-functor clauses are definitional interface claims rather than separate proof steps; no citation entries are required. I checked that the cited enough-injectives node states the exact existence property used, and that all other notions are covered by the listed definition dependencies. I also checked for an existing exact Lean declaration and for duplicate blueprint nodes; neither exists. The only correction was replacing the inherited placeholder Mathlib search results with the results of the required searches actually run on 2026-10-11, and adding the split report, audit metadata, and empty citations file.

## Second reading by E1
The item statement was checked against Stacks Cohomology, Section 20.11, Tag 01DZ (`section-cohomology-sheaves`), lines defining cohomology for an arbitrary ringed space and an $\mathcal O_X$-module; verdict: agrees hypothesis by hypothesis. There are no proof steps because this is a definition; consequently there are no step citations or elementary-step claims to audit. The only node, `def-sc-ringed-space-module-cohomology`, was checked for B1--B7: statement-only, self-contained after its definition dependencies, TeX written once, source tag and label present, and the three recorded searches present in `searches.jsonl`; verdict: pass. The cited `lem-sc-ringed-space-module-sheaves-enough-injectives` statement supplies exactly the abelian category and enough-injectives fact used. Small cases checked: the zero module gives zero cohomology, a field viewed as a one-point ringed space has exact global sections and vanishing higher cohomology, the empty space has zero sections, and $p=0$ is the usual global-sections kernel/cokernel degree. The existing `pqf-def-cohomology` and `def-sc-sheaf-cohomology-functor` nodes were read and are scheme-specific, so neither duplicates this arbitrary-ringed-space definition.

Changes made: corrected the recorded Mathlib search results to match the actual 2026-10-11 search log, retained the empty proof and citations files, and documented the scheme-versus-ringed-space distinction so the duplicate audit is explicit. No mathematical statement or dependency required repair.
