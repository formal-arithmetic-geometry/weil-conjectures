# Stage-1 report: lem-coef-ramified-scalar-exceptional-limit

## Files written

- dag/nodes/sec-six-functors/lem-coef-ramified-scalar-exceptional-limit.json: item, statement unchanged, status split, six proof steps.
- citations.json: verbatim statement quotations for every step/node citation.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. No unit or chapter record is changed: this auxiliary item is not the unit's key statement.

## Attachments

None. Searches by the exact blueprint id and by scalar/exceptional terminology in lean/WeilConjectures found no declaration proving the entire statement, including the actual systems and projection identities. No compiler or Lean writer was used.

## WANTED

None. The proof is an agent assembly of existing statements and the locally available blueprint coefficient-limit route.

## What required correction

The item had an empty proof, not a false statement. Its hypotheses and all five displayed isomorphisms are unchanged. The main mathematical issue was specifying system isomorphisms rather than comparing individual finite levels: the actual reconstruction counits, and their projection-adjoint descriptions, supply those isomorphisms. The ramified intermediate quotients must not be treated as flat over the smaller coefficient quotients. The cited scalar Tor theorem handles them by restriction of scalars.

The current shared DAG contains pre-existing long dependency paths returning from some already stipulated statement dependencies to this item. I checked the paths before constructing the proof. I did not repair other nodes or introduce a new lemma to conceal those paths. The required server checks determine whether the current delivery is admissible.

## What could not be finished

Nothing in the mathematical split remains open beyond the existing dependency nodes. No additional node is needed: each potential auxiliary is either already stated in the DAG or is the explicit two-line tensor reassociation in step 3.

## Not duplicates

No new nodes. Whole-DAG searches found and reused the existing normalized effectivity, arithmetic restriction, scalar constructibility and scalar Tor-bound statements. Blueprint searches for cofinal, exceptional limit, and realization scalar found no blueprint node stating this complete assertion. Its ancestry remains lem-coef-rational-operations through lem-coef-finite-scalar-mate-realization.

## Review by Q131

I read the chapter record sec-six-functors and unit sk-prop-sf-biduality-general. The fixed route assembles integral operations from finite coefficients, then transports them by scalar extension. This proof realizes the finite-free tensor/derived-limit sentence of the current main-20261015 lem-coef-rational-operations proof. I also read the current prop-coef-integral-exceptional-adjoint proof, the current lem-coef-integral-finite-extension proof's first two paragraphs, and the full older normalized-DVR effectivity statement and proof. These explicitly explain why normalization yields the canonical counit comparisons and why cofinal scalar reductions have a uniform interval. I used no SGA source.

For step 1, I opened the complete statements of lem-coef-integral-residue-tor, prop-coef-integral-exceptional-adjoint, lem-coef-normalized-dvr-effectivity and lem-coef-derived-system-evaluation-calculus. The first supplies a single Tor interval; the second states both the actual system-limit construction of G and its output interval; effectivity supplies the coherent projection-adjoint isomorphisms; the evaluation calculus identifies these with the actual counit, and states evaluation conservativity. The item already supplies the normalized system adjunction. I checked that M is integral constructible, f and both schemes have the required finite-type/separated hypotheses, and dimension bounds are nonnegative even on empty schemes.

For step 2, I read lem-weil-integral-scalar-extension-constructible, lem-weil-finite-free-completed-scalar-comparison and lem-pur-adic-scalar-extension-tor-bound. Constructibility is an assertion of the first, not inferred from Tor amplitude alone. The second supplies the canonical chi map and completeness, and the third covers every S-level using en >= m, without imposing flatness at intermediate levels. I read the rationalization definition cited as source by scalar constructibility and the current integral finite-extension proof that explains its integral input. I checked that M and G_R M are in the input domain before applying these results.

For step 3, I read the full K-flat resolution and K-flat change-of-rings statements, as well as Stacks sites-cohomology.tex at lemma-K-flat-resolution (06YS) and lemma-pullback-K-flat (0G7E). They provide the one representative and justify both derived tensor computations. The tensor balancing bijection is written explicitly, commutes with actual quotients and is therefore not an extra lemma hidden under a word such as transport. I read lem-sp-strict-tower-arithmetic-restriction and Stacks more-algebra.tex at lemma-pro-isomorphism-iso-Rlim (0H9K), including the coordinate-selection and finite-block product maps. The existing ringed-site node, not the abelian-group source alone, supplies the projection and cone-unit identity. I also reread the actual reduction unit/counit clauses of the evaluation calculus and chi's explicit quotient-cone construction. Thus the step identifies functors on morphisms, not just their values.

For step 4, lem-coef-finite-adjunction-diagram-realization states the functorial realization of both finite operations and their quotient maps. prop-coef-integral-exceptional-adjoint specifies G to be the limit of precisely E applied to the coherent reduction system. Together with arithmetic restriction these justify the second displayed identification. The first and third are direct substitutions into step 3 and the step-1 counit, not independently asserted comparison theorems.

For step 5, the finite realization statement explicitly says integral compact support is L F R with the specified projections. The compact-support constructibility statement is used only for membership of F_R P. Normalized effectivity and the evaluation calculus make its reduction counit an actual system isomorphism. Applying the specified F functor and then L gives the fourth identification; applying scalar extension to that counit and using step 3 gives the fifth. Every composition has the stated X/Y source and target. I have not used effectivity to assert a false statement that all unbounded normalized towers are constructible.

For step 6, I read lem-coef-ramified-scalar-system-transpose and lem-pur-compact-support-integral-coefficient-comparison in full. The former explicitly constructs alpha-sys as proper coefficient projection followed by open extension tensor comparison on simultaneous sections. The latter explicitly defines its integral comparison as the limit of that same ordered strict-tower composite, with chi and the finite-free normalization. This is the map equality needed; it does not follow from evaluation conservativity. The final sentence uses naturality of the constructions in the evaluation calculus and arithmetic restriction, rather than claiming evaluations are faithful. The fixed compactification is used throughout. No independence-of-compactification argument or exceptional scalar isomorphism is smuggled into this proof.

I checked the delivery-errors B--E cases individually: there are no new statement-only nodes, unresolved definition nodes, or Mathlib leaves to mislabel; each cited statement was opened and its verbatim text is recorded in citations.json; no whole clause is moved to a new node; every non-elementary step cites the relevant assertion. All six steps are under 2000 characters. Off-unit generic tools are declared in split_report.tool_uses. The original statement dependencies were preserved.

The small cases checked were M=0, f=id, either scheme empty, identity coefficient extension, unramified extension e=1 and ramification e>1. For e=1 the restriction comparison is identity as stated. For f=id the formulas reduce to reduction followed by completion and scalar reassociation; no extra geometric identification is needed. For empty schemes the prescribed dimension bounds avoid a negative or undefined bound. For ramification, only equality of ideals is used, so a unit relating uniformizers causes no change. Intermediate m need not be a multiple of e and is handled by the scalar Tor theorem. All constructions commute with the zero maps and shifts through their specified functors.

The five fresh Mathlib queries and their actual results are retained in searches.jsonl and copied exactly into the item's search record. I read the returned ordinary initial-functor limitIso in Mathlib/CategoryTheory/Limits/Final.lean at line 712, the module adic StrictMono.extend and extend_eq in RingTheory/AdicCompletion/Basic.lean at lines 791 and 809, and the general pointwise right-derived HasColimit statement at line 63. They do not state the required derived semilinear-sheaf functor identifications or their compact-support normalization. The second natural-language phrasing likewise returned module adic or local-cohomology constructions. No unavailable service is recorded as a successful negative search.

## Server validation and delivery blocker

The required deliver.py --no-push process exited 1: PREFLIGHT FAILED, nothing pushed. I waited for that invocation to exit before running diagnostics; no push invocation was started. The separate sanctioned server review_split check exited 0 and reported PASS, 0 new nodes, with the declared tool uses accepted. The sanctioned server check_dag check exited 1 with exactly one finding: a cycle component of 124 nodes containing this item. The diagnostic calls also both exited; no delivery or check process remains active.

This is an existing dependency obstruction, not an omitted local proof citation. The unchanged statement already requires prop-coef-integral-exceptional-adjoint. Reading DAG edges gives this return path:

lem-coef-ramified-scalar-exceptional-limit → prop-coef-integral-exceptional-adjoint → lem-coef-finite-exceptional → fix-prop-projection-formula → def-zl-field-weil-shriek-shift-data → lem-pod-semilinear-field-operation-lifts → lem-pod-weil-frobenius-compact-support-exchange → sk-def-sf-exchanges → sk-def-sf-operations → thm-sf-ctf-stability → lem-coef-rational-operations → lem-coef-finite-scalar-mate-realization → lem-coef-ramified-scalar-exceptional-limit.

Removing the first edge would leave the statement's stipulated integral adjunction without its definition/construction dependency. The other edges are in nodes outside this item. I have not changed them, the statement, or any launcher/check script, nor bypassed the check. Maintainer repair of that pre-existing cycle is required before this prepared split can be delivered. Final disposition: BLOCKED by the mandatory server DAG gate.


## Restart verification, 2026-10-23

I retained the previous proof, report, citations and search log and started with the required `deliver.py Q131 lem-coef-ramified-scalar-exceptional-limit --no-push`. That invocation completed with exit 1, `PREFLIGHT FAILED, nothing pushed`. I then ran the sanctioned server diagnostics separately: `check_dag` completed with exit 1 and one finding, the same 124-node cycle; `review_split` completed with exit 0 and `PASS; 0 new nodes`. All three processes exited. No push invocation was started.

I compared the sandbox item with the current read clone: its statement and statement dependencies are unchanged. The live item is still unsplit, has no review record, and has no repair note. Only the six split-owned fields (proof, proof_deps, proof_origin, mathlib_searches, split_report and status) differ. The 25 preserved citation quotations all remain verbatim substrings of the corresponding current node statements. I read the retained search results rather than rerunning unchanged search questions. The fresh project-source search for the blueprint tag and ramified scalar/exceptional terminology found no attachment.

I checked each edge of the return path above in the current repository, independently of the sandbox proof. Every edge is present in the live files. In particular, the item's edge to prop-coef-integral-exceptional-adjoint is already a statement dependency; the path returns to the item via lem-coef-finite-scalar-mate-realization. Consequently changing or removing the newly supplied proof cannot remove this existing cycle. Removing the integral exceptional adjunction from the item's dependencies while its statement explicitly names and uses that adjunction would violate the statement-dependency rule. All other edges on that path belong to other items. The worker brief forbids editing those nodes or changing the gate, so the outstanding blocker requires maintainer repair outside this sandbox. No statement, citation, proof or search record was discarded or altered on this restart.


## Dispatcher retry verification, 2026-10-23T05:14:39+00:00

The required initial dry run completed with exit 1, `PREFLIGHT FAILED, nothing pushed`. After that process exited, the sanctioned server diagnostics completed: `review_split` exited 0 with `PASS; 0 new nodes`; `check_dag` exited 1 with exactly one finding, the same 124-node dependency cycle containing this item. All processes exited; no push was attempted.

I compared the retained sandbox node against the current shared repository again. Only proof, proof_deps, proof_origin, mathlib_searches, split_report and status differ; the statement and statement dependencies remain unchanged. The live item is unsplit and has no review or repair note. All 25 retained citation quotations are still verbatim parts of the current cited statements. I read and retained all five logged search results and reran the project-source search for the exact item tag and ramified/scalar/exceptional terminology; it found no attachment.

I verified every edge of the previously documented 12-edge return path against the current live node files. It exists before the sandbox proof is overlaid. In particular, the edge from this item to prop-coef-integral-exceptional-adjoint is an existing statement dependency, necessary because the unchanged statement explicitly uses its integral constructible adjunctions. The remaining return path is entirely in other items. Editing this proof cannot remove that cycle. The worker's scope prohibits editing those other nodes or bypassing the gate, so maintainer repair is still required. All mathematical work, citations, searches and prior reports are preserved.


## Successful dispatcher retry, 2026-10-23T06:05:44+00:00

The required initial dry run exited 0 and printed `OK (not pushed) deliver/Q131/lem-coef-ramified-scalar-exceptional-limit at 626c400b689: preflight passed`. The earlier cycle diagnostics above are preserved as history; that obstruction no longer blocks the current server preflight. I did not edit other nodes or change any check.

I retained the six proof steps and all search records. The current live item is still unsplit, without a review or repair note. Its statement and statement dependencies match the sandbox. All 25 citation quotations remain verbatim in the current statements and cover exactly every step/node pair. The proof-dependency list is exactly the union of the six use lists; every step is below 2000 characters. The project-source tag and ramified/scalar/exceptional search still finds no attachment.

On this retry I reread the source finite-scalar-extension paragraph and the six steps against the current cited statements. In step 1 residue Tor supplies the common interval and the exceptional theorem supplies the output bound; effectivity and the evaluation calculus identify the actual counit, rather than an arbitrary levelwise comparison. In steps 2 and 3 scalar constructibility checks the domains, the scalar Tor theorem handles all intermediate ramified levels, and K-flat tensor reassociation commutes with the actual quotient maps. Arithmetic restriction explicitly preserves the cone unit and the projections. Steps 4 and 5 apply the stated system realizations and effectivity to those actual reduction systems. Step 6 uses the matching ordered proper/open composite specified in the system-scalar and integral compact-support statements, so it does not infer equality of system maps merely from their evaluations. The identity extension, zero object, empty schemes and ramification cases retain the checks recorded under Review by Q131. No mathematical repair was needed.
