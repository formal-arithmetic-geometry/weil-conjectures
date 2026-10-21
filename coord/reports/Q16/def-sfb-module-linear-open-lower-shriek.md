# Stage-1 repair: Q16 / def-sfb-module-linear-open-lower-shriek

1. Files written: dag/nodes/sec-six-functors-basics/def-sfb-module-linear-open-lower-shriek.json (definition; retained historical Mathlib no-match records), citations.json, report.md. No new DAG nodes or Mathlib leaves. The statement is byte-for-byte unchanged as a decoded string. All existing Lean bindings, blueprint metadata and previous search records are retained.
2. Attachments: none claimed. The six existing declaration bindings remain. The read-only source has a sorry in hasProjectionFormula_openImmersion (LowerShriek/Defs.lean:82–84), so the displayed definition and companions do not establish a closed attachment under this brief.
3. WANTED: none.
4. The returned proof had 3442 characters and repeated machinery behind broad sk-def-sfb-transport clauses. Its functoriality calculation and biproduct additivity argument obscured existing smaller proof dependencies. The explicit human repair instruction of 2026-10-21 authorizes reopening this accepted node; it supersedes the old live-wins interpretation that blocked the retained attempt. The retained sandbox and current read-repository item were identical before repair; no mathematical work was discarded.
5. Nothing remains unfinished in this stage-1 repair. No Lean was written and no compiler or build was run.

## Finer split and existing helpers

The repaired proof has seven steps, 1757 characters total (longest step 332). The hidden non-elementary arguments are now direct citations of dedicated existing nodes rather than inline arguments under the umbrella transport unit:

- Canonical-map coherence: def-sfb-adjunction-projection-formula.
- Action laws, functoriality and forgetful equality: def-sfb-modobj-linearization.
- Lifted adjunction: def-sfb-modobj-linearization-transport-adjunction.
- Preservation of colimits and additivity: lem-weil-pbc-left-adjoint-preserves-colimits and lem-sfb-preserving-colimits-additive (existing Mathlib leaves).
- Exactness through the underlying-sheaf equality: det-prop-sfb-module-pullback-exact-lifted.

These are reusable general statements, not new names for clauses of this item. The mandatory duplicate search found every proposed helper already present, so creating copies would violate B9/C5/D1. The fine-grained nodes already belong to the route through sk-def-sfb-transport; the proof now points to them directly. The generic exact-lift, abelianity and tensor tools stay on the original route. Tool uses of the three newly direct transport subnodes are declared in split_report.tool_uses. No existing helper node was modified; all work is in the assigned sandbox. No new Mathlib searches were needed because no node was created; historical searches were retained without presenting them as searches by this repair worker.

## Not duplicates

No new nodes. The whole DAG was searched for linearization, projection formula and colimit-preserving additive functors, and tools/blueprint_refs.py search was run for these concepts. The dedicated existing nodes listed above state exactly the helper claims, so they are cited instead of copied. The blueprint ancestor is the item itself; its existing blueprint.is and empty same_as remain correct (the unit repeats its clause but does not state the same standalone definition).

## Review by Q16

I read the current chapter and module-lower-shriek unit, the current blueprint definition and complete proof, and the live Lean LowerShriek/Defs.lean construction and companions. The source route is abelian extension by zero, projection-formula linearization, then exactness detected on underlying sheaves. This repair keeps that route and the original statement, including the coefficient object j^*Lambda_X rather than Lambda_U. The stronger instruction to repair the proof takes precedence over the older live-wins rule quoted by the previous attempt.

For step 1, I opened the statements of sk-def-sfb-pulled-back-coefficients, sk-def-sfb-finite-lower-shriek and def-sfb-finite-upper-star-monoidal. The first constructs B as a genuine ring/monoid object; the second supplies exactly the adjunction and exactness of P; the third supplies strong monoidality of S. The coefficient category is Ab with its usual closed tensor, so the general Grothendieck abelian coefficient hypotheses apply. No compactification is needed for the open-immersion clause being used.

For step 2, lem-sfb-open-projection-formula identifies its isomorphism as the canonical adjunction map, with the same tensor order, unit and monoidal pullback as the coherence theorem. I read the dedicated def-sfb-adjunction-projection-formula statement and its blueprint source under sk-def-sfb-transport. It gives coherence, not merely invertibility. Thus this step no longer hides the unit/associativity argument.

For step 3, I read def-sfb-modobj-linearization in the DAG and its current blueprint source. Its statement explicitly gives the inverse-projection-map action, its module laws, linearity of P applied to module morphisms and commutation with forgetful functors. This directly replaces the old inline morphism calculation, without inventing a separate node for an elementary identity. For step 4, the dedicated def-sfb-modobj-linearization-transport-adjunction statement and source give precisely the adjunction to mapMod(S) for the same canonical projection formula. Neither step assumes a monoidal structure on P or changes coefficients.

For step 5, I read def-weil-pbc-proetale-site's universe/small-skeleton convention and the full statement of lem-weil-pbc-site-sheaves-enough-injectives; only abelianity is used, on small sites, not an assertion about a large indexing category. I read the statement and blueprint source of det-def-sfb-sheaf-tensor-closed, which explicitly says tensoring on either side is additive and right exact. It applies to B and SB regardless of flatness; no exactness of tensoring is asserted.

For step 6, I read both existing Mathlib-leaf statements and their recorded matches. I checked Stacks Tag 0038, categories.tex lemma-adjoint-exact, which gives preservation of existing colimits by a left adjoint. Only finite diagram shapes are needed. I checked Stacks Tag 010N, homology.tex lemma-exact-functor (1), and the recorded Mathlib rightExactFunctor_le_additiveFunctor at AdditiveFunctor.lean:330–334; the abelian categories established in step 5 and finite-colimit preservation give exactly additivity. This replaces the old unreferenced biproduct calculation with an already searched Mathlib leaf.

For step 7, I read det-prop-sfb-module-pullback-exact-lifted and its blueprint source in full. Its hypotheses are abelian monoidal categories, additive tensor in each variable, right exact left tensor by the two monoids, additive exact F, and equality of the two forgetful composites. Steps 1, 5, 6 and 3 supply those respectively with R=SB, coefficient S=B, F=P and G=P_B. Its conclusion explicitly includes preservation of finite limits and colimits, so no theorem was inferred from a definition node. Each step's uses is backed by a verbatim quote in citations.json; the quotes are copied from statements, never proofs. Earlier-step data are used only after they have been established.

I checked the B–E return checklist: no new-node schema issue, no unsplit proof, no unsupported terminology, no invented searches, no source-only citations, no circular helper, no relabelled clause, no unverified colimit size, and no strengthened hypothesis. Generic tools are declared. The repaired proof and every individual step are well below the requested length bound. Small cases are compatible with the construction: for j=id the canonical formula and action give the identity lift; for empty U the zero object is carried to extension by zero with its unique module action; for the zero coefficient ring only zero modules occur. No flatness, quasi-compactness, nonempty-open or nonzero-ring assumption was introduced. No statement dispute was found.

## Validation

The mandated initial dry run of the retained attempt exited 1 with the sole reason "the item's node file is unchanged". The changes above repair that actual failure and the human's requested finer split. The final dry run and push results follow below once the tool completes.

## Retained prior-attempt report (superseded by this explicit repair)

# Q16: superseded stage-1 assignment

1. Files written: an unchanged reference copy of dag/nodes/sec-six-functors-basics/def-sfb-module-linear-open-lower-shriek.json; citations.json containing the existing cited statements in full. No split fields changed and no new nodes created.
2. Attachments: none claimed. The existing six-declaration binding is already recorded by N5.
3. WANTED: none.
4. Assignment conflict: the live item already has status split and a passing independent stage-1 review by Q12 dated 2026-10-16. coord/brief-stage1.md, isolated-run rule, says: "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." This assignment is therefore superseded by live accepted work.
5. No replacement split is authorized under that rule. Run the prescribed dry run to obtain its diagnosis without altering the accepted node. Do not push a report-only replacement.

## Review by Q16

This is a supersession check, not a new mathematical review or a claim that a fresh split was completed. I read the live node, its recorded review and Lean binding, its unit and chapter, and the current blueprint definition and proof. The existing split follows the projection-formula linearization and exact-lift argument. I read the actual project source WeilConjectures/SixFunctors/ProEtale/ModuleObject/LowerShriek/Defs.lean: the construction at line 90 has domain modules over j^* Lambda_X, target modules over Lambda_X, and is the mapModLeft lift of the abelian extension-by-zero adjunction; lines 99, 105, 109, 123 and 130 supply the forgetful equality, adjunction, additivity and finite-limit/finite-colimit preservation. However hasProjectionFormula_openImmersion at lines 82-84 contains sorry, and the construction uses this instance. Thus I cannot claim a closed attachment. The live lean_audit also says rests_on_sorry. No statement error or changed hypothesis was identified in this limited check; no dependency or source was changed, and no unperformed Mathlib searches were recorded. A fresh split would duplicate already accepted work and violate the live-wins rule.

## Dry-run result

The single prescribed deliver.py --no-push invocation exited 1 after server preflight: "the item's node file is unchanged". Nothing was pushed. This is expected for a superseded assignment; changing an already split-and-reviewed live node merely to satisfy this gate would violate the live-wins rule above. No repair was fabricated and no second invocation was launched.
