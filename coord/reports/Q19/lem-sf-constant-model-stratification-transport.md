# Stage-1 report: lem-sf-constant-model-stratification-transport

## Files written

- dag/nodes/sec-six-functors/lem-sf-constant-model-stratification-transport.json: item, now split into five elementary witness arguments; Mathlib verdict: no match for the full statement.
- citations.json: nine literal statement excerpts, one for each step/node citation.
- searches.jsonl: actual search-command log, retained unchanged.
- report.md: this report.

No new nodes; no Mathlib leaves. The existing statement, statement dependencies, source, creation record and blueprint ancestry are preserved. Its blueprint.same_as is [] after searching the whole imported blueprint. The proof has no step longer than 2000 characters and its total step text is under 3000 characters. No Lean was written or compiled.

## Attachments

None. Searched lean/WeilConjectures/ by the exact item id, HasFiniteConstantLocalModel, IsConstantModelConstructible, FiniteLocallyClosedStratification, and constructibility/isomorphism concepts. There is no declaration there stating all clauses of the item. The proof helpers in lean/Sheaf/Paper/OpenImmersionLocalizing.lean, lines 47–97, cover individual local-model transport and one direction of record conversion, but are private Sheaf declarations and do not constitute the required whole-item attachment. They were read as corroboration, not offered as finished upstream proofs.

## WANTED

None. The blueprint proof, all defining source paragraphs, and Stacks topology.tex are present locally.

## Problems and corrections

The item is true as stated; no STATEMENT-DISPUTED correction is needed. Its imported proof was empty. Replaced that gap with the explicit record operations, the two maps of every transported local isomorphism, affine-local quantification, and cohomological vanishing argument. No new node is justified for these few-line operations on existing data.

The original blueprint constructibility paragraph describes the passage as locally constant on strata. The present item makes its intended finite constant scalar witnesses explicit. I used sk-def-sfb-constructible and det-def-sfb-constructible-local-model for exactly that convention. sk-def-sfb-derived-categories also discusses a different, weaker constructibility notion allowing arbitrary entries in local presentations: this proof uses it only as an ambient-derived-category statement dependency, and never as the definition of the present Dbc. No Tor-amplitude statement is inferred.

The source Tag 09XZ is topology-definition-paritition (that spelling is the actual label), a partition into locally closed subsets; the project's definition adds finiteness and scheme realizations. I do not introduce the partial ordering from Stacks' different definition-stratification, or claim locally closed subsets are constructible without additional assumptions.

A literal citation initially differed from the node only at a line break ('A' precedes a newline). Corrected the excerpt to the actual statement substring and verified all nine quotes before delivery.

## Unfinished work

None within this stage-1 item. No new statement-only sublemmas are needed. This delivery does not assert a Lean proof.

## Searches and duplicate check

Ran tools/blueprint_refs.py ancestor for the item, and whole-blueprint searches for 'constant model' (zero blueprint matches) and 'stratification' (43 matches). Read the matching definition nodes. Searched DAG nodes for constant-model transport, witnesses and isomorphisms, and stratification conversion, then narrowed to sec-six-functors and sec-proetale-coefficients. The related open-extension-zero constructibility node is an application, not this arbitrary-isomorphism witness adapter. No same-statement blueprint node was found.

Ran the mandatory msearch.py commands with leanfinder, loogle, grep and leansearch, and a second leanfinder phrasing. The log and mathlib_searches record the actual queries and results. LeanSearch found CategoryTheory.Sheaf.isConstant_congr and isConstant_of_iso; read ConstantSheaf.lean:76–93. These concern the essential image of an ordinary constant-sheaf functor, rather than finite scalar models for internal modules with retained covers. LeanFinder found SheafOfModules.IsFinitePresentation and quasicoherent-presentation data; these allow arbitrary coefficients in the ring sheaf and do not express the required scalar-model witnesses. The second phrasing found abstract Finpartition/Partition copying, not scheme strata and module witnesses. Loogle and grep found no matches. No service was reported unavailable.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs.

## Review by Q19

I read coord/brief-stage1.md, stages/1-dag.md, the three-level requirements in SETUP.md, GOAL.md, the worker role and delivery-errors.md B–E (including the duplicated retired-run sections). I read the current chapter and sk-lem-sf-open-ctf unit records. The item realizes only the witness and cohomology-isomorphism portion of the unit's open-extension-by-zero route; it does not replace that route or alter the unit statement. The item is not the unit's key theorem, so no unit realization fields were edited.

For the item source I read main-20261015/blueprint/sec-six-functors/sk-lem-sf-open-ctf/sk-prop-proper-image-localizing-open.proof.md, especially its Constructibility paragraph. For the notions used in the proof I read the source text of sk-def-sfb-constructible, det-def-sfb-constructible-local-model and sk-def-sfb-module-pushforward-pullback in main-20261015, the master definition of def-constructible-stratification, and Stacks topology.tex at definition-paritition (09XZ). I also read the statement of every item statement-dependency, including the ambient-derived-category node, and the constructible-subset definition with Tags 005G/005H/005L. There are no new nodes needing a separate source review.

Step 1 uses def-constructible-stratification only for the finite partition, stratum schemes and immersion fields, all of which its statement gives; def-weil-constructible-subset supplies the additional predicate. The constructibility proofs are copied, never derived from local closedness. Both conversion directions retain every data field, so any predicate P on the schemes and maps is literally unchanged. Proof-field equality uses only proof irrelevance, not a geometric identification. No hidden comparison of scheme structures occurs.

Step 2 uses sk-def-sfb-module-pushforward-pullback only for the pullback functor and det-def-sfb-constructible-local-model for the cover, scalar modules and displayed model isomorphism. I checked the orientation: the map from the restricted N to its retained model is phi_i composed with pullback(e inverse), with inverse pullback(e) composed with phi_i inverse. Functoriality sends both inverse identities to inverse identities, which proves this is an isomorphism without any exactness or preservation-of-finite-presentation claim. Finiteness is retained because the scalar module itself is retained.

Step 3 uses the same pullback functor definition and sk-def-sfb-constructible clause 2. The already proved step 2 applies after restriction to each actual stratum scheme. There is no inference from subset containment to factorization, no refinement and no newly chosen reduced structure. The original constructibility proofs and all covers persist. Step 4 uses those same two node statements, now on each affine open, and clause 2 explicitly states the arbitrary-scheme affine-local convention. The argument requires no qcqs hypothesis on the ambient scheme and no common finite cover or stratification across its affine opens.

Step 5 uses sk-def-sfb-constructible's explicit definition of Dbc as bounded complexes with constructible cohomology. Its constructibility input is established in steps 3 and 4, so no unlisted isomorphism-invariance theorem is used. The isomorphisms to zero outside [r,s] give zero cohomology by uniqueness of maps to and from a zero object. This elementary categorical argument neither invokes a t-structure bound theorem nor asserts finite Tor amplitude.

I tested the empty scheme/empty stratification, one-stratum witnesses, zero scalar modules and the identity isomorphism. Copying works in all these cases; with the identity, the new local isomorphism is the original one. Nonreduced stratum schemes are unchanged. Non-Noetherian schemes require the constructibility proofs as separate inputs throughout. For non-qcqs schemes each affine witness is retained separately. If the interval is empty (r>s), every cohomology is zero by the same outside-interval argument; there is no exceptional degree. These checks expose no missing hypothesis.

Against B–E: no new elementary, duplicate or restated-clause nodes were introduced; the five steps carry the complete argument. Every citation was checked against the cited statement itself and is represented by an exact quote in citations.json. Every operation beyond the cited definitions is a finite record operation, functor inverse identity, composition of isomorphisms, or the defining boundedness condition, so elementary:true is appropriate. No long step hides a lemma; no off-unit theorem, SGA source, new axiom or circular dependency is used. The report records the convention distinction rather than silently conflating the two notions of constructibility.
