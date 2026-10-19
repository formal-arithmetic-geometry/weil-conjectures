# Stage-1 report: def-weil-pbc-finite-stage-pair-category

## Files written

- dag/nodes/sec-proper-base-change/def-weil-pbc-finite-stage-pair-category.json: definition split using existing nodes; no whole-item Mathlib match.
- citations.json: empty list, because this definition has no proof steps.
- report.md: this report. searches.jsonl is produced only by the authorized search command.

## New nodes

None; 0 new nodes and 0 new Mathlib leaves. Reused the existing Mathlib leaves def-weil-finite-subextension-directed-set and def-weil-directed-colimit-abelian-groups.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 checkout for the exact blueprint tag and for FinExt, finite-stage pairs, PairCategory and scalar-extension terminology. No declaration gives the construction. The source itself says in SixFunctors/Etale/Derived/ProjectionFormula/Rational.lean:37-41 and SixFunctors/ProEtale/Derived/ProjectionFormula.lean:75-81 that the finite-stage 2-colimit is not constructed. Upstream master remains reference material, not evidence of a closed proof.

## WANTED

None. The item's actual construction is in the obtained master blueprint. Its source note explicitly says the cited Stacks tags do not state the pair-category construction.

## Corrections and boundaries

This is a definition, so a split consists of naming its inputs, not inventing theorem steps. Added the existing finite-subextension index and directed abelian-group colimit as statement dependencies and citations. Retained bounded-constructible-complete to explicitly fix the inherited domain of T: noetherian, finite dimensional, with ell invertible. The previously unbound prime and algebraic closure are supplied by the finite-subextension node; finite fields mean finite extensions, not fields with finitely many elements. Inclusion symbols in the index are non-strict, as required to include the base field and identity stages. Expanded the final common-stage operations sentence to formulas for addition, zero, negative, identity and composition. These are definitions, not new claims or a change of coefficient category.

The existing prop-weil-pbc-common-stage-calculus states transport functoriality, the equivalence-relation laws, representative independence and additive-category laws. It already depends on this definition. These assertions were not duplicated in new nodes and that theorem was not added as a dependency back on itself through this item. Its proof is not certified by this delivery. In particular its reference to gamma-isomorphisms does not point to data actually given in the present source definition; that downstream proof needs its own review. No gamma-isomorphism theorem is used here.

No unit/chapter route changed. This definition is not the unit's key theorem. The chapter and unit records were read; their realized fields were left alone.

## Blueprint comparison and not duplicates

Whole-blueprint searches for finite-stage pair, finite-stage, common-stage, pair category and Hom colimit were read alongside DAG searches for compositum and colimit notions. def-weil-algebraically-closed-coefficients is a larger Qlbar coefficient-category definition, explicitly using this pair construction; it is not an independent equivalent definition to merge into or cite backward. def-weil-pbc-qbar-category adds Qlbar scalar multiplication; common-stage-cones adds cone/triangle data. None states just this definition independently. Accordingly same_as is empty. No new node was made, so no new/existing same-tag pairs require a Not duplicates comparison.

Read master blueprint sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-finite-stage-pair-category.md, order 1308, in full. The slopmaster2 counterpart is src/version/sketch/42_qbarl_triangulated_colimit.tex: def:finext through def:pair-composition. Its formulas confirm the quotient and operations but its finite stages are rational Karoubi categories; this delivery retains master's raw rational stages def-weil-pbc-rational-category and the normalized transitions of prop-weil-pbc-scalar-extension. No Karoubi envelope, triangles or comparison to a condensed coefficient category was silently inserted.

## Mathlib searches

Every recorded search was actually run using msearch.py; the log is searches.jsonl. Both semantic phrasings and Loogle results were read. LeanSearch returned Internal Server Error and is recorded unavailable. Pseudofunctor provides coherent transition data, not the pair-category quotient. Grothendieck has morphisms over an arrow from the source base to the target base, not an eventual-equality Hom over arbitrary common overfields, so it is not a one-line match. Read the Pseudofunctor structure and Grothendieck structure/Hom in source. The second semantic search found AddCommGroup.DirectLimit and filtered monoid colimits: read Algebra/Colimit/Module.lean:280-335; this supplies the already existing directed-colimit input, not the whole construction. There is therefore no whole-item Mathlib leaf.

## Review by ND

I checked B through E of delivery-errors against the actual definition and source. B: no new statement-only nodes are necessary; the definition names the exact existing notions, all notation is TeX written once, and the searches and unavailable service are recorded faithfully. I read Stacks categories.tex at definition-directed-set (00D3), lemma-directed-category-system (0032), remark-trick-needed (09P8), and proetale.tex at definition-Dbc (09C1), checking the tag-label map. The first defines the directed index notion; the next two discuss colimits in fixed categories, and 09C1 fixes one ring and ideal. None is claimed to construct this category. The blueprint, rather than a spurious Stacks citation, remains the construction source.

C: there are no proof steps, hence no step citations to fabricate. I opened every statement dependency. def-weil-finite-subextension-directed-set states nonemptiness, compositum directedness and finiteness of inclusions, exactly the field-index input needed here. def-weil-directed-colimit-abelian-groups explicitly states representatives and eventual equality, not merely an abstract existence claim. def-weil-pbc-rational-category gives the raw rational Hom groups and objects; bounded-constructible-complete supplies their inherited scheme scope. prop-weil-pbc-scalar-extension gives normalized identity functors, exact functors, the displayed natural associators and their unit/pentagon equations. Those equations, not an unrelated Yoneda or generic colimit theorem, are the specified transition data. No assertion is borrowed from a cited node's proof. Off-unit inputs are definitions or reviewed Mathlib leaves. No downstream category-law theorem is cited as an input, avoiding a cycle.

D: this is a definition-only split under stages/1-dag section 3(2). It does not move a clause to a fresh theorem or claim that applying an unsplit restatement proves it. Equivalence and well-definedness already have their own existing theorem; they remain there. E: I type-checked the transport formula on paper: inverse source associator takes T_(N/E)K to T_(N/M)T_(M/E)K, the functor map lands in T_(N/M)T_(M/F)L, and target associator lands in T_(N/F)L. Composition at P has the identical middle object T_(P/F)L. Tested E=F=M=N (literal unit transport and ordinary identity/composition), equal coefficient fields with different objects, zero objects/morphisms, and incomparable finite fields (their compositum supplies a stage). The indexing set is a subset of subfields of the fixed algebraic closure and hence a set; each rational Hom is taken in its own locally small category, so this is a set-sized Hom colimit in a sufficiently large universe. The construction uses no assumption that transition maps on Hom are injective; eventual equality is essential. These checks found no false mathematical clause in the item.

## Unfinished work

None for this one-level definition split. The scalar-extension theorem and common-stage calculus remain separate existing items; their proofs are not supplied by this delivery. No Lean was written, no compiler or build was run, and no source checkout was edited.

## Dry run

Ran `python3 /home/ubuntu/weil-launcher-nt/deliver.py ND def-weil-pbc-finite-stage-pair-category --no-push`; it printed `OK (not pushed) deliver/ND/def-weil-pbc-finite-stage-pair-category at a4edf6c478: preflight passed`. The source-only baseline comparison correctly ignores the 32 inherited cycles and reports no introduced findings.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against the master blueprint node at order 1308 and the slopmaster2 sketch; all binders (prime, $\Ql$, algebraic closure, and $T$) and the finite-stage, representative, quotient, and common-stage operation clauses are present and correctly scoped.
- Statement dependencies: checked each cited node; the bounded constructible category supplies the scheme hypotheses, the finite-subextension node supplies the directed finite-field index, the rational-category node supplies $\Dbc(T,E)$, scalar-extension supplies normalized units/associators/shift comparisons, and the directed-colimit node supplies eventual-equality representatives.
- Proof steps: none, because this is a definition-only split; no uncited proof fact is hidden in a step.
- New nodes: none; therefore B1--B7 and per-node source/search checks are vacuous. Existing Mathlib leaves and the additional LeanFinder query were checked for possible whole-item matches; none matches.
- Edge cases: checked the base field stage, equal stages, zero objects and zero morphisms, empty/zero morphism classes, and incomparable finite stages via their compositum; all formulas remain meaningful.

The earlier second-reading text claimed that `blueprint.from` was filled. That claim was incorrect: this imported node must retain `blueprint.from = null` under stages/1-dag §6 and tools/blueprint_refs.py. The exact definition places are recorded in `split_report.blueprint`; `same_as` remains the searched empty list. The repair worker corrected this report against the actual node and the current field checker.

## Repair of the mechanical return

The return names no numbered mathematical defect: it records an independent PASS followed by mechanical landing refusal and asks for repair against the current side tip. I reran the authorized dry-run packager against that tip before editing; it printed `OK (not pushed)` at `b83482068c`. Thus the old mechanical refusal is not reproduced, and its precise cause is not supplied by the return. I have not treated a rebase alone as a repair.

Concrete corrections: the old report falsely said that the second reader filled `blueprint.from`; I corrected it and retained null, which the current blueprint checker explicitly requires for imported nodes. All six recorded search dates were 2026-10-14 although the unchanged search receipts say 2026-10-13; the node now agrees with the receipts. Common-stage transport and indexing use explicit non-strict inclusions, consistently with the base-field and identity representatives. These notation changes retain exactly the intended objects and morphisms. No search receipt, maintainer field, or source document was edited, and no new node was introduced.

## Review by ND

For this repair I reread the complete master definition (order 1308), the slopmaster2 definitions `def:finext`, `def:finite-stages`, `def:pair-objects`, `def:morphism-representative`, `def:representative-equality`, `def:pair-hom`, `def:pair-addition`, and `def:pair-composition`, and the unit/chapter records. Slopmaster2 supplies expanded representative formulas but assumes a Karoubi finite-stage category; master's raw rational category is still the one used here. I reread Stacks categories.tex labels definition-directed-set (00D3), lemma-directed-category-system (0032), remark-trick-needed (09P8), and proetale.tex definition-Dbc (09C1). They supply context, not this construction.

I opened the current statements of all five inputs. The finite-subextension node gives finite composita, a nonempty directed set, and finite inclusions; the directed-colimit node gives common-later-stage equality and representatives. The integral complete-category node imposes precisely noetherian, finite-dimensional T with ell invertible. The rational-category node uses those integral categories and raw localized Hom groups. The scalar-extension node gives exact functors, literal identity stages, natural associators, and unit/pentagon equations. The inverse source associator, functor image, and target associator have the domains and codomains displayed in the definition; two transported composable arrows have the same middle object. There are no proof steps and citations.json remains empty. In particular no downstream common-stage-calculus statement is cited backward.

Against B--E, there are no new nodes or new leaf claims, no hidden proof-step citation, and no fresh duplicate or route change. I repeated the whole-blueprint finite-stage/pair search and the project-source attachment search; the projection-formula implementation notes explicitly say the finite-stage 2-colimit is absent. Existing recorded searches agree with their receipts; no unrun search was added. I checked the base field, equal stages, zero morphisms and zero objects, and incomparable fields via their compositum. Explicit non-strict inclusions make the equal-stage cases immediate without excluding them. Every Hom set contains zero, so the earlier phrase 'empty/zero morphism classes' cannot mean an empty Hom set. The repair claims no identification with a condensed coefficient category and leaves category-law proofs to the existing downstream item.

## Repair dry run

After the concrete node and report corrections, `python3 /home/ubuntu/weil-launcher-nt/deliver.py ND def-weil-pbc-finite-stage-pair-category --no-push` printed `OK (not pushed) deliver/ND/def-weil-pbc-finite-stage-pair-category at 3184f07c7d: preflight passed`. No delivery was pushed. This result replaces the old dry-run result for the repaired content. The report is packaged once more after recording this result, so the final accepted sandbox contains this evidence for the second reader.


## Second reading by ND

- Item statement: compared every clause with master definition order 1308 and slopmaster2 labels def:finext, def:finite-stages, def:pair-objects, def:morphism-representative, def:representative-equality, def:pair-hom, def:pair-addition, and def:pair-composition; PASS, preserving master's raw rational categories rather than substituting slopmaster2's Karoubi stages.
- Proof steps: none; checked definition-only splitting against stages/1-dag section 3(2); PASS. citations.json is correctly empty because there are no proof-step citations.
- New nodes: none; checked the sandbox file inventory; PASS, no duplicated, elementary, restated, or unsearched new node remains.
- Coefficient index input: opened def-weil-finite-subextension-directed-set; PASS, nonempty finite intermediate fields, finite inclusions and composita supply all common stages. Its subset notation is inclusive, as its explicit base-field clause confirms.
- Finite-stage inputs: opened def-weil-pbc-bounded-constructible-complete and def-weil-pbc-rational-category; PASS, noetherian finite-dimensional schemes with ell invertible and raw localized integral Hom groups are retained. No hypothesis from the stronger slopmaster2 coherence theorem was silently imported.
- Transition input: opened prop-weil-pbc-scalar-extension; PASS for the exact functors, literal identity transitions, natural associators and unit/pentagon data used here. The source inverse associator starts at T_(N/E)K, the functor image ends at T_(N/M)T_(M/F)L, and the target associator ends at T_(N/F)L. The node's additional exchange assertions are not used by this definition.
- Hom input: opened def-weil-directed-colimit-abelian-groups; PASS, its explicit common-later-stage equality matches the displayed relation. No injectivity of transition Hom maps is assumed.
- Well-definedness boundary: opened prop-weil-pbc-common-stage-calculus; PASS, equivalence, transport equations and representative-independent category operations are already its assertions. It depends on this definition and is not cited backward as an input; this delivery does not certify its unfinished proof.
- Stacks sources: read categories.tex definition-directed-set (00D3), lemma-directed-category-system (0032), remark-trick-needed (09P8), and proetale.tex definition-Dbc (09C1); PASS, they are context only, not falsely represented as a theorem constructing this pair category.
- Duplicate/Mathlib check: independently searched the whole blueprint for pair category and finite-stage, then opened def-weil-algebraically-closed-coefficients, def-weil-pbc-qbar-category and def-weil-pbc-common-stage-cones; PASS, these have different finite-stage data or add scalar/triangle data. Ran a new LeanFinder query phrased using localization of the Grothendieck construction. Read Mathlib CategoryTheory/Grothendieck.lean:65-91 and CategoryTheory/Localization/Construction.lean:90-117; no exact or one-line match. The actual receipt remains in searches.jsonl and its result is now recorded in the item.
- Source attachment check: read slopmaster2 Etale/Derived/ProjectionFormula/Rational.lean:37-43 and ProEtale/Derived/ProjectionFormula.lean:75-81; PASS, they explicitly say the finite-stage 2-colimit is absent. Upstream master is only reference material, never proof evidence.
- Edge cases: checked E=F=M=N=Ql, different objects at equal fields, zero objects and morphisms, and incomparable fields with common stage their compositum; PASS. Composition has identical middle object T_(P/F)L. The empty scheme is not excluded and has the same formal zero-object construction. There is no reduction exponent n in this definition, so n=0 or n=1 imposes no additional case. Every Hom has a zero representative and is nonempty.
- Route and form: opened the unit and chapter records and coord/dag-sync.md/GOAL.md; PASS, no route, target, maintainer field, live project, Lean source, compiler or build is changed.

Changes: made the implicit condition E subseteq F explicit before defining T_(F/E), and defined the associator component notation at K. Both clarify the source formulas without changing the mathematical object. Recorded the independently run Mathlib search with its actual date and result. Preserved all first-worker review sections and all correct construction clauses; introduced no nodes or leaves.
