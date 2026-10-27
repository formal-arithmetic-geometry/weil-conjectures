# Q26: lem-sfb-proper-dc-preserves-continuous

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-dc-preserves-continuous.json`: statement, split into six proof steps; Mathlib search verdict: no match for proper preservation of bounded constructible continuous-coefficient complexes. All dependencies already exist.
- `citations.json`: a verbatim statement quotation for every citation of every proof step.
- `report.md`: this report. `searches.jsonl` contains the actual msearch command log. Local PDF text extracts and `write_split.py` are scratch material only.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiled, no repository or launcher file written, no direct git command run.

## Attachments

None for the item. I searched the project declarations both by its blueprint tag and by bounded-constructible proper pushforward. The exact upstream declaration `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj` in `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/ProperLowerStarEllAdic.lean:67` still has `sorry` at line 74. The standing-scheme declaration `properPushforward_boundedConstructible_rational` in `lean/Sheaf/Paper/ProperBaseChangeRational.lean:245` also has `sorry` and has a narrower geometric scope. Neither is an attachment.

The existing normed coefficient realization is reused as a node, not claimed as an attachment of this item. Its statement includes precisely the derived equivalences, constructibility preservation in both directions, and derived pushforward comparisons needed here.

## WANTED

None. The PDFs and blueprint sources used were already present.

## Statement and source audit

STATEMENT-DISPUTED: the imported scope citation `[sk-def-sfb-dc-setting]` is misleading when used for this upstream declaration. That setting assumes positive characteristic and separated schemes of finite type over k. The upstream declaration instead assumes only a field k with characteristic different from ell, a Noetherian target, and a proper p. For instance, k=Q, ell=2 and p=id on Spec(Q) meet the upstream hypotheses but cannot belong to the cited positive-characteristic setting. Even in positive characteristic, Y=Spec(k(t)), p=id, is Noetherian but its structure map to Spec(k) is not of finite type (Zariski's lemma).

I removed that setting dependency, replaced it with the definitions actually used, and stated the unrestricted structure-map scope explicitly. This corrects the annotation to match the imported item's explicit hypotheses and its upstream declaration; it does not add a hypothesis. A finite normed extension and its normalized norm are spelled out to match `NormedField`, `NormedAlgebra`, and `FiniteDimensional` in the upstream Lean. The conclusion and the ordinary internal-module constructibility predicate are unchanged. The statement also fixes inherited doubled TeX escapes.

The broader proper theorem is not proved by citing `det-thm-sfb-proper-base-change-rational`: that node assumes standing schemes. The original `blueprint.same_as` pointed to that node, which also states two further clauses; I cleared this claim of exact sameness and recorded the restricted overlap in `split_report.blueprint`.

I read the current chapter and the `sk-prop-open-coefficients` unit. The latter explicitly follows proper finiteness for its integral argument and then uses integral models and rationalization for its rational argument. This delivery realizes just that proper finite-field coefficient case, using a model of the entire bounded complex rather than redoing its finite generator induction. It does not replace the chapter route. The item is not the unit's open-immersion key statement, so the unit realization fields are untouched.

## Not duplicates

No new nodes were created. Before considering an embedding/realization lemma I searched the DAG by tags (in particular 09GU), key words, the existing proof of `lem-sfb-dc-lower-star-preserves`, and the whole blueprint using `tools/blueprint_refs.py search` for proper direct image, rationalization, integral and normed coefficients. This located `lem-sfb-normed-coefficient-realization`, which already packages the embedding, norm and category transport, and the existing algebraic-embedding node below it. I discarded the prospective new lemma and reused the existing realization. The existing integral proper sibling is a different coefficient theorem, not a renamed rational clause; it is used only after constructing an integral model and before the independent scalar/push comparison.

## Mathlib searches

I ran msearch with LeanFinder, Loogle, LeanSearch and source grep, and read all returned hits. I tried a second plain-language description of proper finiteness before concluding there was no item match. Hits were ordinary sheaf pushforward, constructible subsets, and proper finite-type consequences; these do not state bounded constructible pro-etale module direct-image preservation. Additional searches tested whether a prospective coefficient-field embedding/realization dependency was already in Mathlib: IsAlgClosed.lift and finite-dimensional continuity were found, then the existing DAG realization was located, so no new leaf was made.

Every query appended to the item's `mathlib_searches` is copied exactly from this session's `searches.jsonl` and records the actual returned names or files. No service was unavailable. The three pre-existing maintainer search records were preserved as inherited history; I do not claim to have rerun those historical query strings. No new node depends on historical unlogged searches.

## Review by Q26

I read Bhatt--Scholze, Theorem 6.7.1 and Lemma 6.7.2 (finite proper input and complete integral preservation), Lemma 6.8.2 (the actual integral coefficients and rationalization), Lemma 6.8.13 and Proposition 6.8.14(2) (integral models), and Remark 6.8.15 (ordinary ambient derived functors). For the scalar/push comparison I also read Hemo--Richarz--Scholbach Lemma 5.3(1), whose common lower-bound condition is applicable to the bounded integral complex. I read the current blueprint rational proper proof, especially its parts (1) and (2), and the scalar-preservation proof. The sources explain the route; the cited node statements, not hidden claims from those proofs, supply every non-elementary assertion in this delivery. No SGA source is used.

Step 1 uses `pqf-lem-proper-basic` for exactly finite type and qcqs of p, and `lem-weil-pbc-finite-type-over-noetherian` for Noetherianity of Z from that of Y. I checked their statements and read Stacks morphisms.tex, definition-proper (Tag 01W0) and lemma-finite-type-noetherian (Tag 01T6). I additionally cited `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, whose statement gives the minimal-element condition on closed subsets and whose source is properties.tex, lemma-Noetherian-topology (Tag 01OZ), to justify the topologically Noetherian hypothesis explicitly. I initially had left this last implication implicit and repaired it during self-review. No finite dimension of Y is inferred or needed.

Step 2 uses the full statement of `lem-sfb-normed-coefficient-realization`. I verified that its E is an arbitrary finite normed extension, its equivalences apply to every scheme, both directions preserve the actual stratified locally finitely presented predicate, and its natural pushforward comparison applies to every morphism. Thus K transports to an embedded field without imposing any geometric assumption. This avoids a fresh embedding node and avoids identifying differently topologized coefficient rings without proof.

Step 3 uses `def-weil-pbc-continuous-integral-coefficients` only for its actual coefficient inclusion, scalar functor and integral category. It uses `lem-weil-pbc-continuous-constructible-integral-model` for the existence of M and the derived isomorphism, including every bounded constructible K, not just a lisse sheaf. Its statement assumes only topological Noetherianity of Z, supplied in step 1. I read the corresponding public declaration in ContinuousConstructibleIntegralModel.lean to verify that it is the same internal-module predicate and an isomorphism in the full derived category. No claim of a global lisse lattice is made.

Step 4 uses the current reviewed statement of `lem-sfb-proper-dc-preserves-integral` for the embedded field F and proper p with Noetherian target Y. On repair I re-read its entire current statement and the upstream integral declaration at ProperLowerStarEllAdic.lean:93--101. The sibling has removed its misleading standing-setting reference, explicitly defined Noetherian as quasi-compact and locally Noetherian, and added references defining pulled-back coefficients and properness. I checked each hypothesis: the prime and invertibility come from the item, the finite embedding of F from step 2, the actual integer-ring coefficient and bounded constructible M from step 3, and properness and the two Noetherian conditions from the item. I rewrote step 4 to exhibit this substitution and replaced its quotation with the full current statement. This uses the integral conclusion only, with no rational-preservation assumption.

Step 5 uses `lem-weil-pbc-continuous-integral-push-comparison` for the specific derivedPushHom isomorphism, with p qcqs and M integral bounded constructible, both already established. Its statement expressly concerns ordinary uncompleted pushforward on any schemes. I read its public Lean declaration and docstring to check that it is this same coefficient inclusion. `lem-sfb-extend-scalars-bounded-constructible` supplies bounded constructibility of the left endpoint T_Y N from step 4. Its statement has no Noetherian or standing-scheme scope restriction, and its actual coefficient map is the embedded integer-to-field inclusion fixed in step 3. No geometric base change or arbitrary coefficient-extension theorem is invoked.

Step 6 is elementary composition of these established isomorphisms and functoriality. I wrote out why the defining boundedness and finite local presentations are invariant under isomorphism, then applied the inverse coefficient equivalence already established in step 2. It uses no uncited devissage, spectral sequence, or hidden comparison. Each step's citations have a verbatim statement in citations.json, and proof_deps is exactly the union of uses. All six steps are shorter than 2000 characters.

For delivery-errors B, there is no new unsplit node, no new notion awaiting a definition, no new Mathlib leaf with unverifiable lines, and no prospective duplicate survives the DAG search. For C, I opened every cited statement, checked the precise scope and functor, recorded every non-elementary input, and checked that none depends on this item. Off-unit generic tools are declared in split_report.tool_uses; no top-level maintainer tool_uses is set. For D, the proof constructs an integral model, uses integral finiteness, and compares its rationalization; none of the steps moves the rational conclusion into a fresh node. For E, no separatedness, absolute finite type, positive characteristic, excellence, bounded dimension or global lisse-lattice hypothesis is silently assumed.

I tested the statements on the zero complex, empty source, empty target (forcing empty source), identity proper morphism, E=Q_ell, ramified finite E, characteristic-zero k, and a Noetherian k-scheme whose structure map is not finite type. The models, coefficient equivalences, and pushforward isomorphisms preserve zero; identity maps give the expected localization comparison. Ramification creates no new condition because the coefficient map is the whole integer-ring inclusion, not an identification ell=uniformizer. No bound on absolute dimension or on the cohomology of k enters.

## Unfinished work

No part of this one-level stage-1 split remains unwritten. Its integral proper dependency is now an existing split-and-reviewed DAG item; this delivery cites its current statement and claims neither a Lean proof of that dependency nor a completed proof of the target. The required remote dry run and final delivery are recorded below when completed.

## Validation

The required remote `deliver.py Q26 lem-sfb-proper-dc-preserves-continuous --no-push` completed successfully: `OK (not pushed)` at `1384a4cbc28`, with the server preflight passed. The check ran through the authorized delivery tool; no forbidden local checker or compiler was invoked. A separate read-only graph traversal confirmed that none of the nine direct dependencies reaches the item, and each citations.json quotation is a verbatim substring of the relevant current node statement. The final dry run includes this validation paragraph before delivery.


## Repair of returned delivery L

The returned retained delivery is `ed48defb253` (the retained dry-run certificate). I compared its saved node and quotations against the current shared DAG, preserving the proof route, original source audit, citations, report and search log. The item on the current DAG remains unsplit; its differences from the saved item are the intended split and scope clarification already reviewed. Among all nine step citations, the integral sibling is the only statement whose quotation no longer matches. The initial required dry run independently diagnosed exactly that stale step-4 quotation and exited without pushing.

I revalidated the integral sibling's changed statement as described under Review by Q26. The changes clarify rather than narrow its Noetherian scope, so the integral-model argument still applies without new hypotheses or new nodes. The current sibling is split and independently reviewed; the obsolete report sentence saying its setting reference remained misleading has been corrected. Step 4 now enumerates the match of every hypothesis instead of merely asserting applicability, and citations.json quotes the actual current statement verbatim. All eight other quoted statements were re-read in full and remain verbatim matches. I preserved all logged Mathlib searches, read their recorded results, and ran no replacement searches because no mathematical statement or search question changed. The delivery tool rebases the repaired node onto the current server DAG; no direct git command is used.

The repair again checks delivery-errors B--E: no new nodes or duplicate clauses; every non-elementary input appears in its step's uses and quotes its statement; finite type and qcqs come from properness, Noetherianity supplies the integral model's topological condition, and the scalar comparison is for the ordinary uncompleted pushforward and the actual coefficient inclusion. Every step remains below 2000 characters. The zero complex, empty source, identity over characteristic-zero k, and ramified finite coefficient extension still meet the same hypotheses; no extra dimension or absolute finite-type assumption enters. No repository, launcher, Lean file or compiler was written or invoked.

## Repair validation

The repaired delivery passed the required server dry run at `d5c95032d43`: `OK (not pushed)`, preflight passed. This replaces the stale-citation failure diagnosed at the start of the repair. A final dry run includes this validation entry before the authorized push. The sandbox contains one changed item node, zero new nodes and zero new Mathlib leaves.
