## Files written

- dag/nodes/sec-six-functors/lem-sf-tensor-hom-coefficient-transposes.json: statement, split into eight steps using existing nodes; not a Mathlib leaf.
- citations.json: 24 verbatim statement quotations, one for each step/citation pair.
- No new nodes. The existing statement, statement dependencies, provenance, prior search records and blueprint ancestor are retained.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and coefficient/transpose terminology. The hits are unrelated scalar, base-change or individual adjunction lemmas; none states every clause of this item. No completed project declaration justifies ATTACH.

## Literature and searches

Read AGENTS.md, GOAL.md, SETUP.md (including the three blueprint levels), roles/worker.md, stages/1-dag.md, coord/brief-stage1.md, delivery-errors B–E in both copies, chapter sec-six-functors and unit sk-prop-sf-biduality-general. No repair note exists. The item source is the master fix-lem-tensor-adjunction.md; read it together with the current main-20261015 sk-thm-sf-package/fix-lem-tensor-adjunction.md and its .proof.md. They give the same five-arrow construction and the final instruction to transpose comparison squares to tensor/counit composites. The proof_origin is agent because the expansion is an argument written here following those blueprint sentences. No SGA source is used.

Before writing, searched the whole DAG by transpose, coefficient, localization and common-stage concepts and read the candidate node statements. Ran blueprint_refs.py ancestor and the whole-blueprint searches “coefficient transpose”, “tensor Hom coefficient”, “internal Hom” and “rationalization”; the latter searches returned the general operations and coefficient nodes, not another statement of this five-arrow compatibility. In particular, lem-sfb-adjunction-transpose-square only treats naturality inside one adjunction; it is not the required coefficient square. Existing lem-coef-evaluation-transpose-coherence supplies the general closed-structure calculation and is used instead of creating a duplicate.

The six new Mathlib searches are recorded by the mandated msearch command in searches.jsonl and appended exactly to the item's mathlib_searches; prior records remain. LeanFinder's second query found mateEquiv_apply, mateEquiv and individual tensor Hom naturality results. Read Adjunction.Basic.lean:160–182 and Adjunction.Mates.lean:84 onward: these construct a single adjunction or mate equivalence, not this chain's specified completed coefficient comparisons or common-stage descent. The other hits concern scalar localization of modules and ordinary ModuleCat adjunctions. Therefore the item is not a one-line Mathlib specialization. No new node requires a search or duplicate-tag comparison.

WANTED: none.

## Problems found and corrections

The item had a statement only and no proof. Its statement is unchanged. Importantly it supposes the chain is defined on full domains and writes the specified endpoint comparisons as isomorphisms. Those hypotheses are retained; this split does not prove a larger constructibility or comparison-isomorphism theorem. A tempting citation of thm-coef-finite-hom would require separated schemes, whereas the item permits finite-type schemes whose structure maps need not be separated. It is unnecessary here: the generic evaluation-transpose calculation proves compatibility without invertibility, and the specified isomorphisms and full domains are already the item's hypotheses.

Another tempting misuse is lem-fix-operation-reduction's finite-quotient Hom clause, which assumes site-perfectness. Step 1 explicitly excludes using that clause for invertibility and cites the general evaluation-transpose lemma for the formal identity. Integral Hom reduction is supplied separately by lem-coef-integral-hom-reduction. I expanded coefficient composition in step 6 to cite actual associator, compact-support and mate-pasting statements rather than infer an operation cocycle solely from compatibility with evaluations.

No statement dispute, route change or new mathematical assertion is hidden in a definition. No Lean was written and no compiler, Lake, local DAG checker or local preflight was run. coord/dag-sync.md referenced by the inherited brief is absent; the dispatcher's live read clone and delivery preflight are the applicable synchronization mechanism.

## Review by NW

I checked the statement and every step against the actual cited statements, not their proofs. The source for this item is the blueprint proof identified above; there are no new-node sources to review. Step 1 takes preservation of associators, evaluations, units and counits from the last sentence of lem-fix-operation-reduction, the evaluation-transpose property and its no-invertibility proviso from lem-coef-evaluation-transpose-coherence, and the unrestricted integral reduction transpose from lem-coef-integral-hom-reduction. Its site-perfectness caveat is essential: none is added to our hypotheses.

Step 2 uses the specified ordinary adjunction in fix-prop-adjunctions and exactly the counit equation in lem-amb-mate-unit-counit. With alpha=p inverse, its types are P'T_Y→T_XP and T_YS→S'T_X. Expanding the inverse Hom bijection as epsilon composed with P(u), then naturality of p, gives the displayed square. Step 3 uses the explicit transpose-of-evaluation sentence of lem-coef-evaluation-transpose-coherence; its strong symmetric monoidal hypothesis is supplied by the specified tensor comparison data preserved in lem-fix-operation-reduction. It works with the completed adjunction assumed in the item and introduces no replacement by ordinary tensor.

Step 4 applies the same counit lemma with left adjoint F=Rf_!, right adjoint E=f^!, and alpha=c_F inverse. Its mate is c_E, so the equation is exactly mu' F'(c_E)=T(mu)c_F inverse. The direction is checked and gives the third arrow's square. Step 5 takes the actual PF compatibility from fix-prop-projection-formula, not from the mere definition of PF; solving d_V T(PF)=PF' d_U gives w' PF'=T(w PF)d_U inverse. It uses the evaluation-transpose lemma again for the fifth arrow. Thus PF is used by precomposition in precisely the direction of Gamma.

Step 6 checks successive changes by their actual cocycles: completed scalar associators from lem-fix-scalar-completion-associator, operation tower compatibility from lem-pur-integral-operations-scalar-extension, compact-support successive reductions from lem-fix-compact-support-coefficient-change, supplied higher-stage transition data from def-exchange-projection, right-adjoint cocycles by lem-weil-pbc-mate-pasting, and the explicit Hom comparison cocycle from lem-coef-evaluation-transpose-coherence. No inference of equality from evaluations of a derived tower is made. Each off-unit statement is declared as a generic tool use in split_report.

Step 7 uses the raw localized Hom formula in def-weil-rationalization-karoubi and R-linear structure in lem-weil-integral-constructible-linear. Linearity follows from naturality in L using scalars and biproducts; no new linear-adjunction lemma is assumed. The explicit pure-tensor formulas give inverse linear maps without any flatness or finite-generation assumption. lem-pur-semilinear-scalar-localization applies because the image of the uniformizer is invertible in the destination coefficient field; its statement explicitly preserves compositions, whiskering and shift equations. Step 8 uses the precise common-stage equality criterion and composition rule in def-weil-algebraically-closed-coefficients and the action on representatives in def-weil-derived-pullback-tensor-hom. It compares representatives after a further common field, rather than assuming any stage functor is faithful. The same finite-stage argument gives inverse maps and equations on their classes.

I checked n=m, identity scalar extension, successive quotient reductions, zero inputs, empty source/target and f=id: each formula reduces to its identity or zero counterpart, with no cancellation by a zero map. A zero or torsion localized Hom module causes no problem for the pure-tensor inverse calculation. A ramified finite field extension is handled by the cited completed associator normalization, not an equality of uniformizer powers. Every proof step is shorter than 2000 characters. Steps 7 and 8 are elementary explicit tensor/colimit arguments from the cited definitions and generic localization theorem. All 24 citation quotes are literal substrings of the current cited statements. A source-only dependency traversal found no path from any cited node back to this item. No new nodes, no restated clauses, no duplicate tags, and no target statement change.

## Not duplicates

No new nodes were created.

## Unfinished work

None within this stage-1 item. The cited existing unsplit obligations remain their own queue items; this delivery proves the assembly relative to their statements.
