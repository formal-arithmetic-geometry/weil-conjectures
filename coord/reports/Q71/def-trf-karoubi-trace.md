## Files written

- `dag/nodes/sec-trace-formula/def-trf-karoubi-trace.json`: definition-only split, using seven existing statement dependencies; no exact Mathlib match.
- `citations.json`: `[]`, because a definition has no proof steps.
- `searches.jsonl`: the actual `msearch.py` log; every recorded query was run.

New nodes: 0. Mathlib leaves: 0. The imported blueprint fields and maintainer-owned metadata are retained. No unit or chapter file is changed.

## Attachments

None. Searches of `WeilConjectures/` in slopmaster2 and the read-only master checkout for the exact id, `karoubiTrace`, and both orders of `trace`/`Karoubi` found no item declaration. The general `CategoryTheory.MonoidalCategory.trace` at `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Rigid/Braided.lean:74` supplies only the underlying composite, not the summand construction and coefficient convention. `DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace` in `CategoryTheory/DerivedCategory/PerfectTrace.lean:86` is a component-supertrace assertion with `sorry` at line 97, and is neither this definition nor an attachment.

## WANTED

None. This split follows the available blueprint definition; no unavailable literature or SGA route is invoked.

## Statement corrected

STATEMENT-DISPUTED: the imported last sentence asserts a block decomposition for an unspecified ambient endomorphism `v`. For `P=E²` in degree zero, take `e=diag(1,0)` and `v=[[0,0],[1,0]]`. Then `ve=v` maps the first summand into the second, so it is not the claimed endomorphism on the first summand plus zero on the complement. This does not refute the intended trace on a summand; it shows that the implicit endomorphism-on-the-summand condition must be stated.

The repaired definition uses the actual Karoubi morphism `u=eue`. This gives `ue=eu=u` directly. Every ambient `v` commuting with `e` gives `u=eve=ve=ev`, hence the displayed source formula `tr_E(ve | P)` is unchanged. Conversely every Karoubi endomorphism occurs by choosing `v=u`. Thus no genuine endomorphism of the summand is excluded. The notation `(eP,ev)` is spelled out using a section and retraction `i,r`, with `ri=1`, `ir=e`, and induced map `rvi`.

The source's old proper-base-change Karoubi-presentation parenthesis is historical: the current `def-weil-pbc-qbar-category` itself now defines a common-stage pair category without completion. The split describes the formal envelope of the specifically named framework category instead, without asserting an equivalence between distinct integral/rational coefficient models.

The original trace dependency `def-trf-categorical-trace` has been specialized by its reviewed statement to finite `A=O_E/varpi_E^n`. It cannot by itself supply an `E`-valued trace. The existing `sk-d-trace` explicitly supplies `Perf(R)`, its derived dual, and the scalar-valued trace for every commutative ring `R`, and is used at `R=E`. The existing perfect-ring-complex and Karoubi definitions now state the inputs precisely. Idempotent completeness is attributed to `lem-weil-qbar-idempotent-complete`, whose statement supplies it, rather than being inferred from the common-stage definition alone.

## What remains

The scalar composite on the presented object is the complete definition. Intrinsic summand interpretation and independence of finite-stage representatives are well-definedness properties, pointed forward to the existing following node `prop-trf-karoubi-independence`, not used as premises of this definition. That proposition already depends on this item; adding it to `stmt_deps` would create a cycle. No clause was repackaged as a new unsplit lemma. Its imported proof should be checked when that node is split: an isomorphism of summands need not be an isomorphism of their ambient perfect complexes (compare the whole one-dimensional complex with a rank-one projector on a two-dimensional complex). The present definition does not use that proof or assume ambient isomorphism.

## Review by Q71

I read the item in both `literature/blueprint/master/blueprint/sec-trace-formula/sk-thm-trace-transport/def-trf-karoubi-trace.md` and the corresponding `main-20261015` file. Their defining text is identical (orders 2397 and 2741). I also read the chapter and unit records and the current generic trace unit `main-20261015/blueprint/sec-trace-formula/sk-d-trace/_section.md`. This realizes the coefficient-stage convention and trace display of field-stage Step 4 of trace transport; it changes no unit statement or route. There are no new nodes requiring additional source readings.

I reopened and read the complete statement of every final dependency. In the introductory paragraph, `def-weil-finite-field-fiber` supplies precisely `p,a,q,k_0,k`, the chosen algebraic closure of `Q_l`, and geometric base change; `def-trf-coefficient-conventions` supplies the separated finite-type `X_0`, `ell != p` and the finite coefficient extension `E`. Only that portion of its convention bundle is used, not its finite-coefficient cohomology construction. `def-weil-algebraically-closed-coefficients` explicitly has finite-stage pair objects, common-stage morphisms, and eventual equality of representatives, with no formal idempotents adjoined. `lem-weil-qbar-idempotent-complete` explicitly states idempotent completeness for exactly those framework finite stages and arbitrary schemes `Y`; specializing to this `X` adds no scheme hypothesis. I did not use the proper-base-change completeness theorem for a different coefficient model.

In the construction paragraph, `def-pc-perfect-ring-complex` defines the required perfect objects in `D(E)` as bounded finite-projective representatives. `def-weil-karoubi-envelope` explicitly gives the morphism condition `u=d u e`; setting the source and target idempotents both equal to `e` gives the condition `u=eue` used here. Its identity is `e`, not `1_P`. `sk-d-trace` explicitly gives the displayed coevaluation, tensor, symmetry and evaluation composite and the specialization to perfect complexes over a general commutative ring. This is exactly the part needed at the field `E`; it does not require a finite ring or a coefficient sheaf. These statements supply every non-elementary input of the definition (C1/C4).

The only calculations retained in the definition are `ue=eue²=u`, `eu=e²ue=u`, and, when `ve=ev`, `eve=ve=ev`. They are consequences of the two displayed input equations, not extra lemmas or proof steps. Given a splitting, `rvi` has type `S -> S`, and `ir=e`, `ri=1` are in the correct order. The source's block-diagonal explanation is valid for the repaired ambient commuting formulation. Intrinsic interpretation remains a subsequent assertion, so this definition has empty `proof`, `proof_deps`, and `citations.json`. I read the statement and proof of `prop-trf-karoubi-independence` to check that it compares compatible summand traces over common finite stages, and left it as a forward reference.

For small cases, `e=0` forces `u=0`; `e=1` gives the ordinary categorical trace; `P=0` gives the zero trace. For `P=E²`, `e=diag(1,0)`, and `v=diag(a,b)`, the formula selects `a` and discards the complement. For a one-dimensional summand in an odd degree, the formula retains the Koszul sign through the same categorical trace, rather than introducing an unsigned matrix trace. No freeness of projective modules over a general ring is assumed: the construction here is over the field `E`. The concrete noncommuting matrix above identified the wording fault and prompted the repair.

I checked delivery-errors B–E against the files. There are no statement-only new nodes to audit, no moved clauses, and no new Stacks-tag duplicates. Whole-DAG searches for trace/summand/idempotent and whole-blueprint searches for `trace`, `Karoubi`, `summand`, `trace on` and `summand trace` found generic inputs and the already existing independence proposition, not another definition of this same trace-on-summand convention. Hence `blueprint.same_as=[]`. I checked the dependency closures of all seven inputs: none depends on this item.

Mathlib was searched through `msearch.py` using both the projector/perfect-complex wording and the retract/splitting wording, with LeanFinder, LeanSearch, Loogle and source grep. LeanSearch was available. I read the module-trace and direct-sum candidates: `LinearMap.trace_eq_sum_trace_restrict` (`Mathlib/Algebra/DirectSum/LinearMap.lean:70`), `LinearMap.IsProj.trace` (`Mathlib/LinearAlgebra/Trace.lean:327`), and the cyclic/product trace formulas in the latter file. They are ordinary-module statements, not the defining derived scalar composite or the coefficient-stage convention. Karoubi homological-complex hits only state projector equations or completeness. None is an exact or one-line whole-item specialization. All actual queries and the returned candidate names are recorded; no unavailable search was called a negative result.

The substantive corrections were the endomorphism condition, the field-valued trace input, the completeness citation, and the obsolete presentation parenthesis. The report distinguishes these from changes of target statements: no target or unit statement was changed. The required dry run is the final verification; no push is authorized for this first reader.

## Second reading by Q71

- Definition statement: reread the complete repaired statement against both blueprint source files (master order 2397 and main-20261015 order 2741); all finite-field, coefficient, category, perfect-complex, idempotent, Karoubi, and trace clauses agree with the intended definition, with the commuting-endomorphism condition made explicit; PASS.
- Proof steps: none, because this is a definition-only split; `proof`, `proof_deps`, and `citations.json` correctly remain empty.
- New nodes: none; no new node requires a separate B1–B7 audit.
- Statement dependencies: reread the seven cited node statements; each supplies the exact notion used in the repaired definition, while the stale finite-coefficient categorical-trace and historical proper-base-change category dependencies were removed as unused; PASS.
- Source correction and edge cases: the noncommuting projector counterexample validates the `u=eue`/commuting-ambient repair; `e=0`, `e=1`, zero complexes, diagonal projectors, and odd-degree signs give the stated zero, ordinary, zero-object, selected-component, and Koszul-trace behavior; PASS.
- Blueprint and Mathlib searches: the imported blueprint identity and empty `same_as` remain correct; the recorded LeanSearch, Loogle, LeanFinder, and grep queries found no whole-item declaration; PASS.

Changes made in this second reading: removed the two unused statement dependencies (`def-trf-categorical-trace` and `def-weil-pbc-qbar-category`) so the dependency list matches the repaired statement; scoped the splitting notation explicitly to the commuting ambient endomorphism; appended this independent audit. No new node or proof step was needed.
