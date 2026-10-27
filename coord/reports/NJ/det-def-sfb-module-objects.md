# det-def-sfb-module-objects — stage 1, NJ, 2026-10-26

## Files written

- dag/nodes/sec-proetale-coefficients/det-def-sfb-module-objects.json — definition, split; generic module-object ingredients are already Mathlib leaves, but no project declaration covers every clause of the whole item. Statement unchanged. Three assembly steps, no new nodes and no new Mathlib leaves.
- citations.json — verbatim complete statements for each of the three cited nodes, indexed by step.
- searches.jsonl — actual msearch.py output records for this run; six queries. No inherited search records.
- report.md — this report.

## Attachments

None. Searched the project for the exact blueprint docstring tag, the node id and the module-object names/concept, and read the coefficient-ring construction in WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean:550–563. AlgebraicGeometry.ProEtale.condensedRingObj at line 560 gives only the pulled-back coefficient object. The generic definitions are in Mathlib, not project declarations stating all parts of the item. The existing Sheaf.AlgebraicGeometry.ProEtaleModuleObjects record belongs to the sheaf-only dependency; it is not a project declaration under WeilConjectures covering the arbitrary monoidal category clauses.

## WANTED

None. The current blueprint sources and all supporting statements are present.

## Problems found and changes

The import already had the correct three assembly citations, but only one paragraph without source locations, no Mathlib searches, no same_as audit, and status imported. I kept the mathematical statement exactly, split the paragraph into three auditable steps, added those existing defining nodes as statement dependencies, supplied source locations and the split report, and recorded the actual searches and results. Nothing was weakened or newly hypothesized. No source error or STATEMENT-DISPUTED issue was found.

The chapter/unit records were read. The live unit record sk-prop-sf-open-closed-triangle still describes an older etale derived triangle in sec-smooth-purity, whereas the current blueprint has the pro-etale open–closed unit in sec-proetale-coefficients. This item's chapter/unit fields and those records were not changed. The item is a supporting definition, not the key statement of that unit, so there are no realized fields to deliver. The proof stays with the current detailed blueprint's three assembly citations and does not replace any open–closed argument.

The required archive glob returned no earlier abandoned attempts for this item, in any group. The sandbox initially had only dispatcher brief markers and no item, report, or searches. No repair note exists for the item.

## Unfinished work

None for this one-level split. Its dependencies are existing live nodes; their further work is outside this item. No Lean file was written and no compiler, Lake or local gate was run.

## Not duplicates

No new node was created. The whole-DAG/blueprint search (`blueprint_refs.py search 'module objects'` and the narrower title query) found sk-def-sfb-module-objects. Comparing its entire statement with this item's statement shows the same three clauses, with parallel ring/tensor/pullback references; it is recorded in blueprint.same_as. I do not create a second module-object definition, category-law lemma or sheaf specialization: the existing det-def-sfb-module-objects-definition, det-def-sfb-module-objects-category and det-def-sfb-module-objects-sheaves supply them. Merging existing imported duplicates is left to the maintainer.

## Review by NJ

I read the current source through literature/blueprint/latest, whose COMMITS.txt entry is main-20261026 at a8806c1f60d0aec15c57e02339aea4bedc0e3759. I read det-def-sfb-module-objects.md and its complete three-sentence proof, together with the current definition, category and sheaves detail files and the unit's _section.md. I checked the live statements of all three proof citations, and also the four original statement dependencies and the sheaf-tensor and pulled-back-ring definitions used in the specialization. No new node needs a source. The assembly is blueprint/agent-written and is marked proof_origin.by = agent.

For step 1, the statement of det-def-sfb-module-objects-definition contains exactly the action R tensor M -> M, the left-unit and associativity formulas, the action-compatible morphism equation, regular action mu, and the specified underlying identities/composition and forgetful maps. It requires only a monoidal category and a monoid object, exactly as the item does. I checked the associator direction: the two associativity composites start at (R tensor R) tensor M and end at M; the unit equation starts at 1 tensor M. The morphism equation has source R tensor M and target N. No additive, commutative, braided or finite-type hypothesis was introduced.

For step 2, I opened det-def-sfb-module-objects-category itself. Clause 1 explicitly gives closure under identity/composition and the category, clause 2 gives a faithful functor (which supplies the functor the item asks for), and clause 3 states that (R,mu) is a module. Thus the category assertions come from a theorem node, not merely from a definition or a construction hidden in somebody's proof. The category lemma's hypothesis is exactly the setting in the preceding definition, so it applies without another assumption.

For step 3, I opened det-def-sfb-module-objects-sheaves: it names the same small pro-etale site, abelian sheaves with the sheafified objectwise tensor over Z, and Lambda_X = p_X^* Lambda, and displays exactly the module category in part 3. I also checked lem-weil-pbc-sheaf-tensor-closed (its symmetric monoidal tensor is precisely a(iota F tensor_p iota G)) and det-def-sfb-pulled-back-coefficients (its statement explicitly makes this pullback a ring object). The detailed sheaves node's tensor-structure and pulled-back-ring references describe those same operations. Accordingly this step is just substitution of C and R, with no comparison between internal modules and an external sheaf-of-rings category. In particular Lambda can be an arbitrary condensed ring: it is not replaced by an ordinary constant ring, a commutative coefficient ring, or a Qbar_l stage. The complete cited statement is quoted verbatim in citations.json, so no implication was attributed to it from its proof alone.

I read the actual msearch hits. Loogle and the second LeanFinder query found the generic Mod/Mod_ constructors, regular object and forgetful functor; the service's deprecated Mod_ names correspond to the pinned Mod names. I read pinned Mathlib/CategoryTheory/Monoidal/Mod.lean:59–65, 102–103, 187–188, 227–230, 300–321, 336–349 and Action/Basic.lean:174–181: the canonical self-action is tensor with the given associator and left unitor, so the general-action definitions specialize directly to this item's first two parts. These are already represented by the two cited Mathlib leaves. The first LeanFinder query and LeanSearch also returned CondensedMod/LightCondMod, Scheme.Modules and SheafOfModules.pullback; I checked their coefficient-category signatures and the defining source snippets. Ordinary coefficient-ring condensed modules and structure-sheaf modules do not state this whole internal pro-etale pulled-back-condensed-ring definition. The second phrasing was thus read rather than concluding absence from the first service result.

I checked delivery-errors B through E against the delivered file. There are no fresh restatements, elementary lemmas made into nodes, or long steps hiding a lemma; all three steps are under 2000 characters and apply existing statements, with their hypotheses checked above. All proof-dependency entries are exactly the union of uses, every use is quoted in citations.json, and the original statement, import flags and blueprint metadata remain. The assembly is not a new-clause relabelling: the cited definition, theorem and specialization pre-exist and the first two are Mathlib leaves. No off-route statement tool is needed (the only cited theorem is itself a Mathlib leaf).

For edge cases I checked the regular object even when the monoid is not commutative, the tensor unit monoid, identities and composites (g f) gamma_M = g gamma_N (R tensor f) = gamma_P (R tensor g)(R tensor f) = gamma_P (R tensor (g f)), and the empty-scheme specialization. All use the same category axioms and the given monoid laws; none needs nonemptiness or qcqs. For abelian sheaves the zero ring also creates no exception: the definition's unit/action conditions still specify its modules, and the regular object exists. These checks did not require a statement repair.
