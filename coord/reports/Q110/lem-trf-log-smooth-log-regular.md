# Q110 repair: lem-trf-log-smooth-log-regular

Date: 2026-10-22. Stage 1 only; direct delivery. The assigned sandbox had only dispatcher brief markers and no retained node, report or search log. I copied the current shared-repository item, which contains exactly the nine returned steps (9093 characters), and continued that version. No git command was run in the shared repository, no source/library file was written, and no compiler or Lake command was run. The first required dry run exited because report.md was absent; it did not stay running.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-log-smooth-log-regular.json: existing statement, unchanged; split, five assembly steps totalling 2877 characters.
- dag/nodes/sec-trace-formula/lem-trf-polynomial-log-chart-regularity.json: new statement, unsplit, no Mathlib match; owns old steps 2--3 (2008 characters of argument).
- dag/nodes/sec-trace-formula/lem-trf-toric-chart-strict-local-preparation.json: new statement, unsplit, no Mathlib match; owns old steps 4--5 (2484 characters of argument).
- dag/nodes/sec-trace-formula/lem-trf-formal-chart-geometric-regularity.json: new statement, unsplit, no Mathlib match; owns old steps 6--7 (2274 characters of argument).
- citations.json: one verbatim statement quotation for every node in every parent step's uses list.
- report.md: this repair report and the full retained arguments below. The sandbox also holds search-plan.json, actual msearch outputs, searches.jsonl, source text extracts, dag-searches.txt, returned-proof.json and reproducible sandbox-only editing scripts. They are working records, not extra DAG nodes.

## Attachments

None. I searched the project declarations under lean/WeilConjectures for the item tag and for logarithmic regularity/smoothness, and searched the relevant Sheaf algebraic-geometry/trace-formula sources for each extracted notion. The item declaration AlgebraicGeometry.logSmooth_logRegular at lean/Sheaf/AlgebraicGeometry/LogSmoothLogRegular.lean:229 ends in sorry (line 245 in this read clone). Its long docstring is the returned argument, not a finished proof. No exact finished upstream declaration for the item or any new node was found.

## WANTED

No additional source is needed for this extraction: I read the available ILO statements and Stacks inputs. Kato 1994, Theorems 3.2 and 8.2, and Kato 1988, Theorem 3.5, are not claimed to have been read; the inherited source already identifies the unavailable chart-criterion reference. The formal chart/model theorems continue as the existing independent DAG inputs, not as an uncited application of an unavailable proof.

## What was wrong and what changed

The human's return is a work-distribution fault: the 9093-character proof is too large for one proof worker. The mathematical statement is unchanged, including all chart hypotheses and the dense/divisorial conclusions. I did not replace the old argument by a compressed sketch. Its six central steps are assigned to three new independent work items, with all their technical outputs explicitly stated: coordinate characteristics and strata; toric face quotient and the unit-twisted completed sharp chart; formal dimension and regularity descent together with the geometric strict-local identification. None is split recursively: proof=[], proof_deps=[], proof_origin=null, status=unsplit. No node states the whole item or its entire log-regularity conclusion under the original arbitrary chart hypothesis.

The parent retains its original factorization argument (old step 1), the explicit ring identification of the intermediate chart (old step 2), the strict-smooth argument (old step 8), and the divisorial/pair assembly (old step 9). A minor explicitness correction in the new preparation statement records that Z and Z_A are locally Noetherian, since their chart rings are finite type over the Noetherian base; this supplies the target Noetherianity used by the strict-smooth stalk lemma.

The existing chapter and unit records were read and left alone. The current unit sk-i-curve-zero uses the contracting-correspondence route; the item's historical ancestry through lem-trf-local-term-locality is retained exactly as recorded, not replaced by a new route. Each child's blueprint.from adds the item to the ancestor's via list and identifies the extracted argument. Whole-blueprint searches for log regular, log regular polynomial, R_G, unit character, monoid completion, and coordinate did not identify an imported blueprint node with a new child's complete statement. DAG statement searches and nearby Lean declarations were inspected before creation.

## Mathlib searches

For each new id I ran msearch.py with a natural-language LeanFinder query, Loogle name patterns, a Mathlib grep, LeanSearch, a second semantic phrasing and a second grep. Every query is copied literally from the command's searches.jsonl entry into that node, together with the actual answer digest and returned names. All services answered; none was marked unavailable. The output files contain the signatures I read. Ordinary smoothness, affine-space coordinates, scheme stalk maps and Grothendieck groups do not state any of the fs logarithmic assertions; the other semantic hits are number-field real logarithms and unit characters in a different sense. Thus there are three new unsplit nodes and zero Mathlib leaves. The old item's logged searches are retained unchanged rather than invented or relabelled.

## Review by Q110

I read coord/delivery-errors.md B--E in full and checked the extraction against the actual statements and sources, rather than relying on the old acceptance annotation. The primary source for the item is ILO Expose VI 1.2, 1.4, 1.6, 1.8 and the final chart in 1.9, printed pp.69--71 (PDF pp.75--77). VI 1.8 gives log-smooth preservation; VI 1.4 gives density and the structural divisorial equality. The parent still proves the precise injective, torsion-free chart case it originally stated.

For lem-trf-polynomial-log-chart-regularity, I read ILO VI 1.8--1.9 and Stacks 031E (algebra.tex, lemma-flat-over-regular-with-regular-fibre) and 00ON (lemma-dimension-base-fibre-equals-total). I also opened the statement of lem-trf-smooth-geometric-stalk-algebra: its affine-space clause really supplies the quotient by any set K of coordinates vanishing in the maximal ideal, the flat local quotient map, regular closed fibre F_K and dim F=dim F_K+|K|. Thus the two applications of the flat dimension formula are licensed. The coordinate pushout gives the direct sum of the base characteristic and N^K; a nonunit factor cannot become a unit in the local ring. The theorem is not just the slogan that polynomial log charts are regular: it states the characteristic and nonunit ideal and fibre calculations a worker has to establish.

For lem-trf-toric-chart-strict-local-preparation, I read VI 1.6 and VIII 3.1.1--3.1.5, printed pp.98--99 (PDF pp.104--105), and the existing fs-face, sharp-chart, completed-chart and Noetherianity statements. The old corrected stratum formula uses the group rings Z[G^gp] and Z[F^gp], not a tensor product over the sharp characteristic rings. The prime of the lift contracts to m_A, so A->B is local and reflects units; this proves h^(-1)(F)=G. Inverting F and killing its complement gives exactly Z[F^gp], with the induced localization prime. The chart a is allowed to be replaced, as the completed-chart statement explicitly permits. Its equality of characteristics yields a unique unit quotient in the integral log stalk; cancellation makes this quotient multiplicative, and R_G^gp=R^gp extends it to epsilon. This retains every compatibility needed by the formal extension model. I explicitly included the Noetherianity of Z and Z_A, besides A and B.

For lem-trf-formal-chart-geometric-regularity, I read ILO VI 1.6 and the full statements of lem-trf-formal-monoid-extension-model and lem-trf-formal-monoid-ring-dimension. The group map is an isomorphism, the local prime lies over m_A, the face equality is assumed, and the chosen sharp chart and unit character are compatible with the displayed completion. These are exactly the model's hypotheses, including mixed characteristic with a regular parameter modulo the nonzero monomials. The dimension theorem gives both dimensions with e=0 or e=1 and regularity of D or D/(eta-bar). I read Stacks 00MA (lemma-completion-tensor), 07NY (lemma-completion-regular), 07NV (lemma-completion-dimension), 05WS (lemma-quotient-strict-henselization), 06LN (lemma-henselization-regular), and 06LK (lemma-henselization-dimension). I opened each corresponding existing node. J is generated by nonunits and lies in m_B, so the quotient and strict-henselization comparison apply. I opened lem-trf-ind-etale-strict-local-invariance: its statement explicitly includes arbitrary base change of the structural strict-local map and an isomorphism over the original scheme. This is the needed geometric identification, not an assertion that an ordinary localization equals a geometric stalk. The new statement records the monomial/ideal compatibility and both regularity and dimension after this identification.

For parent step 1, I opened lem-trf-fs-chart-free-factorization and lem-weil-pbc-etale-smooth-zero-dimensional-fibres: the first supplies actual q_i in Q, an injective h and an isomorphism on group completions, including r=0; the second supplies precisely the smoothness needed for the allowed etale branch. The fs product condition is componentwise in def-trf-fs-log-blowup. For step 2 the new polynomial statement supplies all log-regularity and Noetherianity assertions; the tensor calculation is written explicitly and uses the chosen q_i. For step 3 the preparation and recognition statements match in W,R,Q,h,A,B,G,F,S,T,a,epsilon and completion, so no hidden hypothesis is passed between them. They assert the quoted facts in their statements, not merely in planned proofs.

For parent step 4 I opened all four cited statements. def-trf-fs-log-blowup defines the associated geometric pushout, nonunit ideal and rank/dimension condition. lem-trf-smooth-geometric-stalk-algebra gives Noetherian flat local maps A->B and A/I->B/IB, with the same regular closed fibre, for the smooth comparison; I is contained in m_A. lem-weil-pbc-flat-over-regular-with-regular-fibre gives regularity of B/IB from regularity of A/I. lem-weil-pbc-flat-height-formula states exactly dim B=dim A+dim F and the analogous quotient formula. I also read Stacks 01VF (morphisms.tex, lemma-smooth-flat) and 01VB (lemma-base-change-smooth), the ordinary smoothness inputs underlying the existing geometric-stalk node. For step 5, lem-trf-log-regular-divisorial-structure states both open density and the equality through the structural map. def-trf-log-regular-pair makes this the pair with D=X minus U. These are every non-elementary fact used in the five assembly steps; citations.json quotes their exact statements.

I checked B1--B10: each child is statement-only, introduces all its objects, defines face localizations and formal monoid notation inline, cites the log/geometric/ring notions it needs, has actual searches, and has complete blueprint ancestry. No proposed match was silently promoted to a leaf. I checked C1--C8: every non-elementary parent input is a cited statement; no proof-internal object is borrowed; exact statement quotes are in citations.json; the existing general log-smooth nodes are not used to create a cycle. The retained ordinary commutative-algebra tool uses in the parent split_report are exactly those still cited by the parent. The new unsplit nodes have no proof route edges yet.

I checked D1--D5 against the explicit return: the three children each package a distinct argument of similar former proof length (2008, 2484, 2274), not the item's whole assertion, and all three are cited by the parent. None is a mere elementary two-line lemma: they respectively require geometric coordinate-fibre algebra; face localization plus completed sharp-chart alignment; and formal monoid regularity with completion/strict-local descent. No argument is dropped, as the exact original texts below show. No parent step exceeds 2000 characters; the longest is the retained strict-smooth calculation.

For E1--E7, small cases were checked algebraically. For the polynomial child, r=0 is the identity, K empty leaves only the base log ideal, and a point with all coordinates zero adds exactly r to the characteristic rank and fibre codimension. Empty Y gives empty W. For the preparation child, the identity chart h=1 recovers the original stratum, R=Q a group gives S=T=0, and a nontrivial blowup chart N^2 -> <e1,e2-e1> can change sharp ranks, so the statement correctly does not claim injectivity or equal rank on sharp monoids. No arbitrary h is assumed flat. For the recognition child, T=0 gives a regular ordinary local ring; equal characteristic has e=0; V[[x,y]]/(p-xy) has quotient V/(p) and e=1, producing the expected rank-two logarithmic dimension. The model requires eta-bar in m_D minus m_D^2, excluding a spurious regularity assertion for an arbitrary hypersurface. All geometric checks use strict local rings with compatible base points. Empty chart base change is handled by having no point to check. No statement dispute or source error was found, and no source prohibited by the route lock is cited.


### Repair of the L promotion return (current DAG rebase)

I continued the retained Q110 split and its search log. The opening paragraph above records the original extraction session; this continuation did not start over. The current shared item has the same statement, statement dependencies and all nine proof steps as returned-proof.json. Comparing the parent fields shows only proof, proof_deps and split_report differ. The released stage-1 keep_plan repair note still requires three statement-only work items and an assembly of at most 3000 characters, so the older reviewed record does not supersede this repair. The delivery command builds the commit on the current origin/sheaf-dag and preserves maintainer-owned fields; this is the requested rebase rather than a replay of the old commit.

I re-read every current statement cited by the five assembly steps, including the three retained child statements. Step 1 obtains an explicit injective h and group-completion isomorphism from fs-chart-free-factorization, and the etale comparison is smooth by etale-smooth-zero-dimensional-fibres. Step 2 uses the polynomial child's locally Noetherian fs log regular conclusion; the tensor-ring identification is explicit in the assembly. In step 3 the preparation supplies the faces, local rings, chart, unit character and completed presentation required by the formal-chart recognition node, with h^gp an isomorphism from step 1. Step 4 uses the current smooth-geometric-stalk-algebra statement with compatible geometric points and I contained in the maximal ideal; both flat local maps have the same regular fibre. The regular-fibre ascent statement and the local specialization of the flat-height formula give exactly regularity and the displayed dimension equality. Step 5 uses the divisorial theorem's open density and structural identification, followed by the pair definition. Every retained citations.json quotation remains verbatim in the current statements.

For the extracted arguments I also re-read the current face sharpening, sharp and completed chart, formal monoid extension, formal monoid dimension, closed-immersion strict-localization and ind-etale strict-local invariance statements. Their hypotheses still match the saved argument allocation. I re-read ILO VI 1.2, 1.4, 1.6, 1.8--1.9 and VIII 3.1.1--3.1.5 in the retained extracts, and Stacks algebra.tex labels lemma-dimension-base-fibre-equals-total (00ON), lemma-flat-over-regular-with-regular-fibre (031E), lemma-completion-tensor (00MA), and lemma-quotient-strict-henselization (05WS). No logarithmic or local-algebra conclusion is imported from a cited node's proof instead of its statement. The coordinate r=0 and K empty cases, identity/group charts, and the rank-two mixed-characteristic model remain as tested above.

The first new dry run stopped at a same-tag duplicate check: lem-sfb-ind-etale-henselian-regular-stages now occurs among the 031E matches. I opened its statement: it starts with an ordinary regular Noetherian ring and an ind-etale target and concludes ordinary regularity and regular-sequence properties. It has no logarithmic characteristic, nonunit ideal or polynomial log-stratum formula; it does not replace the polynomial child. Its explicit pair comparison is added under Not duplicates. This is a new review against the current DAG, not an unchanged re-push. I inspected the decoded TeX strings and newline: they are already correctly escaped, so the five mathematical assembly texts need no alteration. The exact historical argument text in this report remains intact. No new Mathlib search was needed because none of the three child statements or search questions changed; I reused the recorded outputs and unavailable/no-match verdicts.

### Current promotion-return continuation after preflight 56a2f97672f

The retained delivery was tested first, as requested: the server dry run exited successfully with `OK (not pushed)` at 56a2f97672f. I then compared the sandbox item with the current shared item field by field: only proof, proof_deps and split_report differ; statement and stmt_deps agree, and returned-proof.json is exactly the current nine-step proof. The three extracted ids are still absent from the current shared DAG. Thus this repair still supplies three new work items rather than overwriting a live completed split. The released keep_plan repair note is still in force.

I re-read the current parent dependencies and the statements supporting all six extracted old steps, alongside ILO VI 1.2, 1.4, 1.6, 1.8--1.9 and VIII 3.1.1--3.1.5 in the retained source extracts. In particular the current smooth-geometric-stalk-algebra statement names the canonical strictHenselizationMap and requires compatible geometric points and I contained in the maximal ideal. I made these explicit in assembly step 4. Its two maps have the same closed fibre, so the regular-fibre ascent applies to A/I -> B/IB, and the current flat-height statement specializes at the two maximal ideals to the displayed dimension equality. Step 1 now expressly retains the injectivity of h supplied by the factorization statement. This is an adjustment of the assembly to the current cited interfaces; none of the mathematical statements or search questions changed.

Every citations.json quotation was checked as an exact substring of the current cited statement, including the retained child statements; the entries cover every step/node pair. The child statements retain all the old coordinate, face/unit-character, formal-model and geometric-stalk outputs. I re-read the saved search results instead of repeating their queries: the logarithm hits concern number fields and the geometric hits concern ordinary smoothness/stalks, not fs log strata. All retained search services answered successfully and all three child verdicts remain no match. The existing Sheaf theorem logSmooth_logRegular still has sorry, and the project upstream search found no completed exact declaration, so attachment is not applicable.

The parent remains below 3000 characters and every step is below 2000. Empty charts, r=0, K empty, identity/group charts and the regular-parameter mixed-characteristic case have the same hypotheses and conclusions as in the review above. The final dry run and push below use the delivery tool's current-base worktree; no git command or write was made in the shared repository and no launcher script was changed.

### Promotion-return repair, 2026-10-23

The initial dry run of this continuation exited with a duplicate-check failure, not a running push: the current DAG now also has lem-sfb-dvr-binomial-local-geometry and lem-sfb-smooth-trait-curve-local-properties sharing 00ON. I opened both entire statements. The first assumes a DVR and studies the hypersurface xy-pi^e; the second assumes a smooth relative curve over a DVR and computes ordinary regularity and local dimension. Neither states the polynomial logarithmic characteristic, nonunit ideal or coordinate fibre formula; their two explicit comparisons have been added under Not duplicates. This is the new-current-DAG repair diagnosed by the required first dry run.

I compared every field of the current shared item with the retained sandbox: the only differences before this edit were proof, proof_deps and split_report. The current nine-step proof still equals returned-proof.json exactly, and all three extracted ids are absent from the shared DAG. The released stage-1 keep_plan re-split note remains in force. I re-read every parent citation from the current DAG and all statements used by the saved extracted arguments, in particular the canonical strict-henselization-map and coordinate clauses of smooth-geometric-stalk-algebra, the chart replacement permitted by log-regular-completed-chart, and the arbitrary-base-change clause of ind-etale-strict-local-invariance. The five assembly steps still match those statements. I made the chart factorization hypotheses explicit in step 1 and named the q_i actually supplied by that node, since step 2 uses them in the tensor relations. This removes an implicit choice from the assembly while retaining the proof route and every child statement.

I read ILO VI 1.2, 1.4, 1.6, 1.8--1.9 and VIII 3.1.1--3.1.5 in the retained extracts. These respectively give the geometric-stratum definition, dense divisorial structure, completed models, smooth preservation/chart application, and monoid localization and sharpening. The child arguments and the local-algebra inputs remain allocated as in the full review and exact old text below. The zero-coordinate and empty-stratum checks still apply, and the mixed-characteristic recognition still assumes a regular parameter rather than an arbitrary hypersurface equation. The project-source keyword/tag search found no finished exact declaration; the existing Sheaf logSmooth_logRegular theorem at line 229 ends in sorry at line 245. I reused and read the retained search log and actual query outputs; none of the child statements or Mathlib search questions changed, so no searches were invented or repeated. Every citations.json entry is checked against the current statement and covers its step/node pair. The assembly remains under 3000 characters, with no step over 2000. The delivery tool will construct the repaired commit on its current server base, preserving maintainer fields; no repository or launcher write and no compiler command is part of this repair.

### Resumed promotion-return repair after provider interruption

The interrupted invocation was checked before any repeat: the opening dry run exited with `OK (not pushed)` at c57d323625a, and no delivery remained active. I compared the current shared item again: its statement and statement dependencies still agree with the retained item, and returned-proof.json exactly equals its nine-step proof. The three extracted ids remain new. The repair note is still released for stage 1. The delivery tool reconstructs this retained split on the current server base.

I re-opened every current statement cited by the five parent steps, plus the face sharpening, sharp/completed chart, formal monoid model and dimension, completion quotient/regularity/dimension, strict-henselization regularity/dimension/Noetherianity, closed-immersion strict-localization and ind-etale invariance statements supporting the extracted arguments. I read ILO VI 1.2, 1.4, 1.6, 1.8--1.9 and VIII 3.1.1--3.1.5 in the retained extracts and the Stacks source statements at 031E, 00ON, 00MA, 05WS, 07NY, 07NV, 06LN and 06LK. These interfaces still match the retained extraction. Step 3 now expressly applies formal-chart recognition to the same W,R,Q,h,A,B and compatible chart data from preparation, with the group-completion isomorphism from step 1; this spells out the assembly rather than leaving that matching implicit.

I verified all 12 citation entries against current statement text and exact coverage of the step/node pairs. The 18 recorded child searches all match searches.jsonl; I read their results and reused them because neither child statements nor search questions changed. The upstream project keyword/tag search has no exact completed declaration, and the existing Sheaf logSmooth_logRegular theorem still ends in sorry. The r=0, empty K, unit-only charts, empty chart base changes and mixed-characteristic regular-parameter cases remain covered. Each child remains statement-only, all old arguments remain below, and the parent assembly has 2877 characters with no step longer than 2000. No source, library, repository or launcher file was written, and no compiler was run.

## Not duplicates

lem-trf-polynomial-log-chart-regularity vs lem-trf-polynomial-strict-local-coordinate-dimension: the existing node treats ordinary polynomial rings over a field, their coordinate quotients and strict henselizations, proving regularity and coordinate codimension. The new node starts over an arbitrary fs log regular base, possibly singular as an ordinary scheme, and computes the logarithmic characteristic, nonunit ideal, flat local stratum map and log dimension formula. The existing field calculation is an input to the already cited smooth-geometric-stalk-algebra theorem, not the logarithmic polynomial assertion.

lem-trf-polynomial-log-chart-regularity vs lem-sfb-dvr-binomial-local-geometry: the existing statement computes ordinary local regularity, cotangent spaces and dimensions of R[x,y]/(xy-pi^e) over a DVR; it gives no arbitrary log regular base, logarithmic coordinate characteristic or nonunit-ideal/coordinate-fibre formula.

lem-trf-polynomial-log-chart-regularity vs lem-sfb-smooth-trait-curve-local-properties: the existing statement concerns ordinary smooth relative curves over a DVR and their regular local rings of dimension at most two; it does not treat arbitrary log regular bases, arbitrary r, or the characteristic and coordinate-boundary stratum calculations of this child.

lem-trf-polynomial-log-chart-regularity vs lem-sfb-ind-etale-henselian-regular-stages: the existing theorem assumes a regular Noetherian source and an ind-etale target with regular fibres; it proves ordinary regularity and regular sequences, whereas this node starts with a possibly singular log regular base and proves the logarithmic characteristic, nonunit ideal, flat coordinate fibres, and log dimension formula.

lem-trf-polynomial-log-chart-regularity vs lem-sfb-log-smooth-preserves-log-regularity: that general log-smooth theorem does not state the coordinate characteristic, nonunit ideal, flat quotient maps or fibre codimension formulas; this node is the concrete coordinate argument needed to prove the chart theorem, not a second general preservation theorem.
lem-trf-polynomial-log-chart-regularity vs lem-per-log-smooth-invertible-torsion-log-regular: the latter is a general log-smooth preservation conclusion and currently depends on the item; it does not supply this coordinate-stratum calculation. Using it would be circular.
lem-trf-polynomial-log-chart-regularity vs lem-trf-smooth-geometric-stalk-algebra: the existing statement concerns ordinary smooth geometric local algebra and coordinate fibres; it does not compute the logarithmic characteristic and ideal or conclude the logarithmic dimension condition.
lem-trf-polynomial-log-chart-regularity vs lem-trf-polynomial-ring-regular-base: ordinary polynomial regularity over a regular ring does not address a possibly singular log regular base or its log characteristic and strata.
lem-trf-toric-chart-strict-local-preparation vs lem-trf-fs-face-sharpening: the existing statement concerns monoids alone; it does not identify local scheme strata, compare charts up to a unit character or construct completed log charts.
lem-trf-toric-chart-strict-local-preparation vs lem-trf-log-regular-sharp-chart: the existing statement gives a sharp chart but no toric stratum tensor formula, unit character relative to the prescribed R-chart, or compatible completed presentation.
lem-trf-toric-chart-strict-local-preparation vs lem-trf-log-regular-completed-chart: the existing statement gives a completed sharp local chart; it does not compare a given nonsharp R-chart by a unit character or describe the base-changed stratum.
lem-trf-toric-chart-strict-local-preparation vs lem-trf-log-chart-face-tor-comparison: that node assumes a sharp chart and a chosen monoid section and concludes a Tor isomorphism; this one prepares the sharp completed chart and a stratum of an arbitrary chart base change, with no Tor assertion.
lem-trf-toric-chart-strict-local-preparation vs lem-trf-formal-monoid-extension-model: the existing node assumes the compatible sharp chart, completion and unit character that the preparation constructs; it concludes a completed target model rather than the face-stratum preparation.
lem-trf-formal-chart-geometric-regularity vs lem-trf-formal-monoid-extension-model: that node stops at a completed pair isomorphism; this one includes dimension and regularity descent, quotient strict henselization and the monomial-compatible isomorphism to the original geometric stalk.
lem-trf-formal-chart-geometric-regularity vs lem-trf-formal-monoid-ring-dimension: the existing statement is about a formal monoid ring over a given coefficient ring D; this one identifies an ordinary base-change localization and its geometric stalk and transports both regularity and dimension to it.
lem-trf-formal-chart-geometric-regularity vs lem-sfb-completed-tame-monoid-base-change-model: the more general tame model likewise stops at the completed target pair; it does not give the geometric strict-local, quotient regularity or dimension conclusions here.
lem-trf-formal-chart-geometric-regularity vs lem-per-completed-invertible-kummer-monoid-extension: the existing statement is a Kummer completed-model result, without the geometric identification or stratum/dimension descent. Here no Kummer hypothesis on R->Q is made.
lem-trf-formal-chart-geometric-regularity vs lem-trf-ind-etale-strict-local-invariance: the existing statement is the generic ind-etale strict-local isomorphism; this node additionally obtains monoidal completed models and regularity/dimension of their strata.

The delivery duplicate gate also listed the following same-tag pairs. I opened every existing statement; sharing 00MA, 00ON or 031E identifies common algebraic inputs, not equal conclusions.

lem-trf-formal-chart-geometric-regularity vs lem-per-completed-etale-jacobian-torsion: the existing theorem constructs a completed polynomial presentation and an annihilator estimate for a finite generically etale algebra; it has no fs chart, monomial stratum, geometric-stalk comparison or log-regularity conclusion.

lem-trf-formal-chart-geometric-regularity vs lem-pod-adic-limit-finite-modules: the existing theorem concerns finite modules over the valuation ring of an l-adic field and their inverse systems; it has no toric chart ring or logarithmic/geometric regularity assertion.

lem-trf-formal-chart-geometric-regularity vs def-weil-pbc-coherent-formal-modules-affine-quotient-cone: the existing node defines a cone of formal module sections; it states no local ring regularity, monoid model or geometric-stalk theorem.

lem-trf-formal-chart-geometric-regularity vs lem-weil-pbc-affine-formal-map-limit-dictionary: the existing theorem algebraizes a map between coherent formal modules and identifies its sections; it does not compute monomial strata or their geometric local dimensions.

lem-trf-formal-chart-geometric-regularity vs lem-weil-pbc-affine-global-formal-comparison: the existing theorem identifies the finite-module and coherent-formal-module categories on a completed affine scheme; it does not give regular toric strata or strict-local comparisons.

lem-trf-formal-chart-geometric-regularity vs lem-weil-pbc-coefficient-subring-principal-source: the existing theorem constructs a complete local coefficient subring as an image of a local PID; it gives none of the toric chart model, dimension or geometric-stalk conclusions.

lem-trf-formal-chart-geometric-regularity vs lem-weil-pbc-coherent-formal-modules-affine-complete: the existing theorem proves one natural isomorphism for finite modules under a formal-module equivalence; it has no logarithmic local algebra or geometric-stratum conclusion.

lem-trf-formal-chart-geometric-regularity vs lem-weil-pbc-coherent-formal-modules-affine-quotient-cone: the existing theorem says the explicit cone of sections of a finite completed module is limiting; it does not identify a completed toric ring, its regular quotient or its strict localization.

lem-trf-formal-chart-geometric-regularity vs lem-weil-pbc-complete-local-quotient: the existing theorem asserts completeness and Noetherianity of a proper quotient of a complete local ring; it does not assert its regularity, monoidal dimension formula or geometric-stalk identification.

lem-trf-formal-chart-geometric-regularity vs lem-weil-pbc-completed-affine-coherent-iso-lift: the existing theorem lifts a linear isomorphism of sections to coherent sheaves on an affine completed scheme; it does not concern toric local strata, their dimension or strict henselizations.

lem-trf-formal-chart-geometric-regularity vs lem-weil-pbc-completion-exact-finite-modules: the existing theorem is exactness of completion on finite modules; this is an input to quotient completion, not the formal toric and geometric regularity statement.

lem-trf-formal-chart-geometric-regularity vs lem-weil-pbc-completion-finite-extension: the existing theorem decomposes the completed tensor product for an algebra finite as a module; no such finiteness is assumed for A->B here, and it does not give logarithmic-stratum regularity or dimension.

lem-trf-polynomial-log-chart-regularity vs lem-weil-pbc-completion-dimension: the existing theorem preserves the Krull dimension of a Noetherian local ring under completion; it does not compute characteristics, coordinate strata or their regularity on a polynomial log chart.

lem-trf-polynomial-log-chart-regularity vs lem-weil-pbc-flat-fiber-local-depth: the existing theorem is a depth formula for a flat algebra and fibre; the new theorem gives a log characteristic, monomial ideal and regular-stratum dimension statement, with no depth assertion.

lem-trf-polynomial-log-chart-regularity vs lem-weil-pbc-flat-fiber-prime-height: the existing theorem is the ordinary height formula for a flat algebra and fibre; it does not identify the logarithmic characteristic or the coordinate vanishing stratum.

lem-trf-polynomial-log-chart-regularity vs lem-weil-pbc-flat-height-formula: the existing theorem supplies the ordinary dimension equality for a flat local map; the coordinate characteristic and log ideal computations and regularity assertion of the new theorem are additional work.

lem-trf-polynomial-log-chart-regularity vs lem-weil-pbc-flat-over-regular-with-regular-fibre: the existing theorem ascends ordinary local regularity under a flat map with regular closed fibre; it does not compute the logarithmic characteristic or polynomial coordinate stratum.

lem-trf-polynomial-log-chart-regularity vs lem-weil-pbc-polynomial-presentation-height-field-extension: the existing theorem compares prime heights under field extension of a presented algebra; it gives no fs log chart, nonunit ideal, coordinate-fibre statement or log regularity.

lem-trf-polynomial-log-chart-regularity vs lem-weil-pbc-pth-root-cotangent-dimension: the existing theorem compares cotangent dimensions of an algebra adjoining pth roots of field elements; this polynomial log chart involves ordinary independent coordinates and characteristic monoids, not that finite inseparable quotient.

lem-trf-polynomial-log-chart-regularity vs lem-trf-smooth-local-tangent-cone-extension: the existing theorem describes associated graded rings and minimal-prime dimensions for essentially smooth local Q-algebras; the new theorem works over arbitrary locally Noetherian log regular bases and computes logarithmic strata.

lem-trf-polynomial-log-chart-regularity vs lem-per-regular-pair-alteration-pullback: the existing theorem pulls a regular alteration covering and a strict normal crossings boundary along a regular morphism; it neither treats general possibly singular log regular bases nor states the coordinate characteristic and stratum formulas.

lem-trf-polynomial-log-chart-regularity vs lem-weil-pbc-regular-map-ascent: the existing theorem ascends ordinary regularity along a flat algebra with regular fibres; the new theorem starts with a possibly nonregular log regular base and computes its coordinate logarithmic strata.

## Exact argument allocation from the returned proof

The following is the returned proof verbatim, grouped by its new owner. It is retained in the report so that parallel workers receive the complete existing argument without proof steps being inserted into unsplit node JSON. Existing cited nodes retain their own statements and proofs; the extracted nodes are responsible for using those inputs, not duplicating them.

### Parent factorization and final assemblies

Old step 1:

Work on any of the etale chart neighbourhoods in the hypothesis. If the comparison is etale, it is smooth by [lem-weil-pbc-etale-smooth-zero-dimensional-fibres]. Apply [lem-trf-fs-chart-free-factorization] to $g:P\to Q$, obtaining $R=P\oplus\mathbf N^r$ and an injective $h:R\to Q$ with $h^{\rm gp}$ an isomorphism. Both $R$ and $Q$ are fs: for $R$ the finite generation, cancellation and saturation conditions hold componentwise. This reduces the monoid change to adjoining coordinate generators followed by extending a monoid inside its own group completion. No injectivity on sharp characteristic monoids is asserted or needed.

Uses: lem-trf-fs-chart-free-factorization, lem-weil-pbc-etale-smooth-zero-dimensional-fibres, def-trf-fs-log-blowup.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI 1.9, final injective-chart test; algebraic factorization supplied by the agent.

Old step 8:

The comparison $c:X_0\to Z$ is smooth by hypothesis and step 1. Its log structure is the pullback of the associated $Q$-chart: both structures are obtained by associating a log structure to that same chart, and the universal pushout defining associated stalks gives the identification. At a geometric point of $X_0$ over one of $Z$, write $A=\mathcal O_{Z,\bar z}$, $B=\mathcal O_{X_0,\bar x}$, and $I\subset A$ for the nonunit log ideal. A local ring map has inverse image of the units equal to the units; hence the associated-stalk pushout identifies the two characteristics, of rank $\rho$, and the source nonunit ideal is $IB$. By [lem-trf-smooth-geometric-stalk-algebra], $A\to B$ and $A/I\to B/IB$ are flat local maps with the same regular closed fibre $F$. Log regularity of $Z$ gives regular $A/I$ and $\dim A=\dim(A/I)+\rho$. Now [lem-weil-pbc-flat-over-regular-with-regular-fibre] makes $B/IB$ regular, while two applications of [lem-weil-pbc-flat-height-formula] give
$$\dim B=\dim A+\dim F=\dim(A/I)+\rho+\dim F=\dim(B/IB)+\rho.$$
Thus $X_0$ is log regular. The charts cover the geometric points of $X$, so the geometric-stalk definition gives log regularity of $X$ itself.

Uses: def-trf-fs-log-blowup, lem-trf-smooth-geometric-stalk-algebra, lem-weil-pbc-flat-over-regular-with-regular-fibre, lem-weil-pbc-flat-height-formula.

Source: literature/stacks-project/algebra.tex; Tags 031E and 00ON, applied to the strict smooth comparison in ILO VI 1.8.

Old step 9:

Apply [lem-trf-log-regular-divisorial-structure] to the locally Noetherian fs log regular scheme just obtained. Its triviality locus $U$ is open dense and the structural map identifies $M_X$ with $\mathcal O_X\cap j_*\mathcal O_U^\times$. Put $D=X\setminus U$. This identification gives exactly the divisorial log structure of [def-trf-log-regular-pair]; it is fs, log regular, and has triviality locus exactly $U$. Consequently $(X,D)$ is a log regular pair, including the empty-scheme and empty-boundary cases.

Uses: lem-trf-log-regular-divisorial-structure, def-trf-log-regular-pair.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI 1.4, printed p. 69; VIII 3.4.1, printed p. 110.

### lem-trf-polynomial-log-chart-regularity

Old step 2:

Take an affine chart $Y_0=\operatorname{Spec}C$ on the chosen base neighbourhood and put $W=\operatorname{Spec}C[t_1,\ldots,t_r]$, with associated log chart $R=P\oplus\mathbf N^r\to C[t]$ sending $(p,(n_i))$ to $\alpha(p)\prod_i t_i^{n_i}$. This is an fs log structure by [def-trf-fs-log-blowup]. The polynomial algebra is finite type over the Noetherian ring $C$, so [lem-weil-pbc-finite-type-algebra-noetherian] makes $W$ locally Noetherian. Expanding finite sums of monomials gives $\mathbf Z[R]=\mathbf Z[P][t_1,\ldots,t_r]$, and hence
$$W\times_{\operatorname{Spec}\mathbf Z[R]}\operatorname{Spec}\mathbf Z[Q]
=Y_0\times_{\operatorname{Spec}\mathbf Z[P]}\operatorname{Spec}\mathbf Z[Q]=:Z.$$
On rings the identification sends $c\otimes[q]$ to itself, and evaluates $t_i$ as $[q_i]$; these maps are inverse because the tensor relations already impose $t_i=[q_i]$.

Uses: def-trf-fs-log-blowup, lem-weil-pbc-finite-type-algebra-noetherian.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI 1.8--1.9, chart reduction; explicit monoid-ring calculation.

Old step 3:

We check that $W$ is log regular. At a geometric point $\bar w$ over $\bar y$, put $A=\mathcal O_{Y_0,\bar y}$, $B=\mathcal O_{W,\bar w}$, and let $I\subset A$ be the ideal of the nonunit base log sections. Set $K=\{i:t_i\in\mathfrak m_B\}$, $k=|K|$, and $\rho=\operatorname{rank}\overline M_{Y_0,\bar y}^{\rm gp}$. The associated-chart pushout in [def-trf-fs-log-blowup] shows directly that the characteristic at $\bar w$ is $\overline M_{Y_0,\bar y}\oplus\mathbf N^K$: the other coordinates map to units, whereas a product involving a nonunit factor cannot be a unit in a local ring. Thus its nonunit ideal is $J=IB+(t_i:i\in K)$ and its rank is $\rho+k$. The coordinate assertion of [lem-trf-smooth-geometric-stalk-algebra] gives flat local maps $A\to B$ and $A/I\to B/J$ with regular closed fibres $F$ and $F_K$, where $\dim F=\dim F_K+k$. Since $A/I$ is regular, [lem-weil-pbc-flat-over-regular-with-regular-fibre] makes $B/J$ regular. Applying [lem-weil-pbc-flat-height-formula] to these two maps gives
$$\dim B=\dim A+\dim F=\dim(A/I)+\rho+\dim F_K+k=\dim(B/J)+\rho+k.$$
This is precisely the definition of log regularity at $\bar w$.

Uses: def-trf-fs-log-blowup, lem-trf-smooth-geometric-stalk-algebra, lem-weil-pbc-flat-over-regular-with-regular-fibre, lem-weil-pbc-flat-height-formula.

Source: literature/stacks-project/algebra.tex; Tags 031E (lemma-flat-over-regular-with-regular-fibre), 00ON (lemma-dimension-base-fibre-equals-total); coordinate case of ILO VI 1.8.

### lem-trf-toric-chart-strict-local-preparation

Old step 4:

Fix a geometric point $\bar z$ of $Z$ and let $\bar w$ be its image in $W$. Set $A=\mathcal O^{\rm sh}_{W,\bar w}$ and $Z_A=\operatorname{Spec}A\times_W Z$. The point lifts to $Z_A$ using the chosen geometric base point. Let $B=(A\otimes_{\mathbf Z[R]}\mathbf Z[Q])_{\mathfrak q}$ at this lift; this is an ordinary local ring over the strict local base $A$. The ring $A$ is Noetherian by [lem-sc-strict-henselization-noetherian], and $B$ is Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian] and [lem-weil-pbc-localization-noetherian]. Put $F=\{q:[q]\in B^\times\}$ and $G=h^{-1}(F)=\alpha^{-1}(A^\times)$; the equality holds because $A\to B$ is local. These are faces. By [lem-trf-fs-face-sharpening], $S=R_G/G^{\rm gp}$ and $T=Q_F/F^{\rm gp}$ are sharp fs with finite free group completions. Set $I=(\alpha(r):r\notin G)A$ and $J=([q]:q\notin F)B$. Inverting $F$ and killing its complementary monomials leaves precisely $\mathbf Z[F^{\rm gp}]$; on the base it inverts $G$ and kills $R\setminus G$. Thus
$$B/J\cong\left((A/I)\otimes_{\mathbf Z[G^{\rm gp}]}\mathbf Z[F^{\rm gp}]\right)_{\mathfrak p},$$
with $[g]$ acting by $\alpha(g)$ and the induced prime $\mathfrak p$. The associated-stalk pushout [def-trf-fs-log-blowup] identifies the characteristics with $S$ and $T$. The same characteristics persist under strict henselization, since local maps reflect units.

Uses: lem-sc-strict-henselization-noetherian, lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian, lem-trf-fs-face-sharpening, def-trf-fs-log-blowup.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI 1.8, corrected face-localized stratum calculation; VIII 3.1.1--3.1.5.

Old step 5:

Step 3 gives log regularity of $W$, so at its geometric point $\bar w$ the ring $A$ already satisfies regularity of $A/I$ and $\dim A=\dim(A/I)+\operatorname{rank}S^{\rm gp}$. Apply [lem-trf-log-regular-sharp-chart] to choose a chart $a:S\to A$ inducing this characteristic, and then [lem-trf-log-regular-completed-chart]. Allow the latter's replacement of $a$ by another chart inducing the same characteristic. It gives a monomial-compatible presentation of $\widehat A$ as $k[[S]][[t]]$ or $V[[S]][[t]]/(\theta)$, with $\theta\equiv p$ modulo the nonzero monomials and the parameters. The original localized chart $\alpha:R_G\to A$ and $a\circ(R_G\to S)$ lift the same characteristic. In the associated integral log monoid their quotient is a unique unit; these units multiply, by cancellation. Hence there is a character $\epsilon:R^{\rm gp}\to A^\times$ such that $\alpha(r)=\epsilon(r)a(\bar r)$ for $r\in R_G$. Extending from $R_G$ to its group completion gives the indicated domain $R^{\rm gp}$. This explicitly retains the possible unit twist rather than assuming that the two chosen charts coincide.

Uses: def-trf-fs-log-blowup, lem-trf-log-regular-sharp-chart, lem-trf-log-regular-completed-chart.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI 1.6; ordinary/geometric local comparison uses Stacks 05WS, 06LN, 06LK.

### lem-trf-formal-chart-geometric-regularity

Old step 6:

The homomorphism $h:R\to Q$ has isomorphic group completions by step 1. Its inverse unit face at $\mathfrak q$ is exactly $G$, as checked in step 4, and the completed presentation of $A$ is compatible with the sharp chart $a$ and unit character $\epsilon$ constructed in step 5. Apply [lem-trf-formal-monoid-extension-model]. It gives, with the same $T=Q_F/F^{\rm gp}$ and the nonunit ideal $J$, a pair isomorphism
$$(\widehat B,J\widehat B)\cong(H,L)\quad\hbox{or}\quad(H/(\eta),L(H/(\eta))),\qquad H=D[[T]],$$
where $D$ is complete regular local, $L$ is generated by the nonzero $T$-monomials, and in the second case $\overline\eta\in D$ is a regular parameter. Apply [lem-trf-formal-monoid-ring-dimension]. Writing $e=0$ in the first case and $e=1$ in the second gives
$$\dim\widehat B=\dim D+\operatorname{rank}T^{\rm gp}-e,\qquad\dim(\widehat B/J\widehat B)=\dim D-e.$$
The same node makes the stratum quotient regular (it is $D$ or $D/(\overline\eta)$). These equalities give both dimension bounds. No finiteness or flatness of $A\to B$, and no asserted chain of monomial primes, is used.

Uses: lem-trf-formal-monoid-extension-model, lem-trf-formal-monoid-ring-dimension.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI 1.6 models used for the independent toric calculation; formal monoid extension and dimension inputs are explicitly separated.

Old step 7:

By [lem-weil-pbc-local-completion-quotient], $\widehat B/J\widehat B$ is the completion of $B/J$. Both rings are Noetherian local, so [lem-weil-pbc-completion-regular-local] and [lem-weil-pbc-completion-dimension] give regularity of $B/J$ and
$$\dim B=\dim(B/J)+\operatorname{rank}T^{\rm gp}.$$
The closed-immersion theorem [lem-trf-closed-immersion-strict-localization-cartesian] identifies $B^{\rm sh}/JB^{\rm sh}$ with $(B/J)^{\rm sh}$. By [lem-sc-strict-henselization-regular] and [lem-sc-strict-henselization-dimension], the quotient is regular and the same dimension equality holds for $B^{\rm sh}$. Finally [lem-trf-ind-etale-strict-local-invariance], explicitly including arbitrary base change of the structural map of a strict localization, identifies the strict localization of $Z_A$ at the lifted geometric point with that of $Z$ at $\bar z$. Thus $B^{\rm sh}=\mathcal O_{Z,\bar z}$ canonically; the identification is over $Z$ and preserves each chart monomial and its nonunit ideal. The characteristic remains $T$ by step 4 and [def-trf-fs-log-blowup]. This proves log regularity of the $Q$-chart on $Z$. If the chart base change is empty there are no points to check.

Uses: lem-weil-pbc-local-completion-quotient, lem-weil-pbc-completion-regular-local, lem-weil-pbc-completion-dimension, lem-trf-closed-immersion-strict-localization-cartesian, lem-sc-strict-henselization-regular, lem-sc-strict-henselization-dimension, def-trf-fs-log-blowup, lem-trf-ind-etale-strict-local-invariance.

Source: literature/stacks-project/more-algebra.tex; Stacks 00MA (completion-tensor), 07NY (completion-regular), 07NV (completion-dimension), 05WS (quotient-strict-henselization), 06LN, 06LK.

## What remains unfinished

The three child proofs are intentionally left unsplit for separate workers, as the return requires. They have no Lean module or code in this delivery. There is no remaining stage-1 repair issue identified by my review. Delivery is subject to the required final remote dry run and push; their outcomes are recorded below when available.

### Current-base repair following dry run 3a0f6f211fa

The required opening dry run finished successfully with OK (not pushed) at 3a0f6f211fa. I compared the current shared item with the retained sandbox field by field: statement and stmt_deps agree, only proof/proof_deps/split_report differ, and returned-proof.json equals the current nine-step proof. All three extracted child ids remain absent from the current DAG; the released stage-1 keep_plan repair still requires this extraction. The delivery tool rebases the repaired files on its current server base.

I read every current statement cited by the five parent steps. Step 1 uses the actual q_i, injective h and group-completion isomorphism supplied by fs-chart-free-factorization, with the etale-to-smooth implication for the allowed etale comparison. Step 2 uses precisely the polynomial child's Noetherian fs log-regular conclusion; the ring maps impose t_i=[q_i]. Step 3 uses the preparation's local map at a prime over m_A, its face equality and its compatible sharp chart/unit character/completion as the inputs of formal-chart-geometric-regularity. I made the compatible source and base chart neighbourhoods explicit in step 1 and the prime-over-maximal-ideal condition explicit in step 3. This discharges the return with a current-base comparison and an adjusted assembly, retaining the approved three child statements.

For step 4 the current smooth-geometric-stalk-algebra statement uses compatible geometric points and the canonical strictHenselizationMap, and allows every I contained in m_A. Its two flat local maps have the same regular closed fibre. Regular-fibre ascent applies to A/I -> B/IB, and the maximal-ideal specialization of flat-height-formula gives both displayed dimension formulas. Step 5 takes density and structural divisorial equality from log-regular-divisorial-structure and checks the pair definition's exact triviality locus. Every one of the 12 citations.json entries is verbatim in its current statement, and their step/node pairs cover exactly the proof uses.

I re-read ILO VI 1.2, 1.4, 1.6, 1.8--1.9 and VIII 3.1.1--3.1.5 in the retained extracts, and the current face-sharpening, sharp/completed-chart, formal monoid model/dimension, completion quotient/regularity/dimension, strict-henselization Noetherianity/regularity/dimension, closed-immersion strict-localization and ind-etale invariance statements supporting the saved old arguments. I also checked Stacks algebra.tex at 031E, 00ON, 00MA and 05WS, and more-algebra.tex at 07NY, 07NV, 06LN and 06LK. In particular arbitrary base change is included in ind-etale invariance, and the completed-chart statement allows replacing the chosen sharp chart. The empty chart and r=0 cases impose no extra condition; unit-only faces have rank zero; mixed characteristic still requires a regular parameter, never an arbitrary hypersurface.

The current upstream declaration search found no completed exact theorem; the Sheaf logSmooth_logRegular theorem still ends in sorry. I read the retained actual search results and checked all 18 child query/tool pairs against searches.jsonl. They concern ordinary smoothness, stalks, group completions or number-field logarithms and do not supply these fs logarithmic statements. Neither the three child statements nor their search questions changed, so their recorded searches are reused. The parent remains below 3000 characters and has no step over 2000. No library, repository or launcher file was written, and no compiler or agent was started.

The next dry run stopped at a newly landed same-tag node, lem-trf-polynomial-strict-local-coordinate-dimension (00ON). I opened its full statement: its source is a polynomial ring over a field and its outputs concern ordinary regular local rings and coordinate codimension, including strict henselization. It does not compute log characteristics or log ideals over a potentially singular log regular base, so it neither states nor generalizes the polynomial child. The explicit pair comparison is now under Not duplicates. The new node belongs to the re-split of smooth-geometric-stalk-algebra; that current theorem's coordinate clause was already read and supplies exactly the ordinary fibre input used by the retained polynomial argument. No child statement or search question changed.
