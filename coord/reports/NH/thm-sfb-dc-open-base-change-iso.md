# Stage-1 report: thm-sfb-dc-open-base-change-iso

## Files written

- dag/nodes/sec-six-functors-basics/thm-sfb-dc-open-base-change-iso.json — statement, split; no exact Mathlib match. Three proof steps use two existing component lemmas and the exchange definition.
- citations.json — verbatim statement excerpts for every step/node citation.
- searches.jsonl — seven searches recorded by msearch.py; their queries and actual result names are retained in the item.
- report.md — this report and NH's self-review.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: the assigned theorem is one clause of the definition unit, not its key definition node. No Lean is written or compiled.

## Attachments

None. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint tag, boundedConstructibleOpenImmersionLowerShriekBaseChange, and open/base-change terminology found no declaration with this statement. The ordinary etale open-extension results have a different site/coefficient setting and are not attachments. The exact upstream-master analogue, AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange, in WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/LowerShriek/MorphismDefs.lean:180, ends in sorry at line 182. It is reference material, not a finished proof.

## Literature and WANTED

No WANTED document. I read the current main-20261015 chapter record, the complete sk-def-sfb-open-base-change unit record and _section.md, the theorem file, and def-sfb-dc-open-base-change-morphism.md. The theorem file supplies only the assertion, with no proof. The upstream-master docstring at lines 173–179 gives the geometric support/stalk motivation, but it is not used as a proof of a module-object or derived comparison. The actual geometric inputs are the already-existing DAG component statements. The short categorical assembly is written out as an agent proof. No SGA source is used and no new Stacks-based lemma is introduced.

## Corrections and scope

The statement is unchanged and is not disputed. Its sole statement dependency still identifies the precise unit-square-counit exchange.

The inherited proof cited stage3-sfb-open-base-change-left-inverse and stage3-sfb-open-base-change-right-inverse, each of whose statement dependencies includes this theorem. Those references close immediate DAG cycles. I removed these two proof dependencies and instead used stage3-sfb-open-base-change-component-mono and stage3-sfb-open-base-change-component-section, which already exist in the same unit and whose dependency closures do not reach this theorem. I did not modify their statements or proofs. The resulting argument does not rely on naturality of the sections: it proves naturality after cancellation.

The seeded proof_origin.by was H3; it is now agent, identifying the actual argument. All maintainer fields and blueprint import metadata are retained. The whole-blueprint searches for open-base-change and extension by zero found the encompassing definition unit and other constructions, but no distinct theorem with exactly this assertion; same_as is therefore [].

## Not duplicates

No new nodes were created. In particular, no new inverse lemma, generic componentwise-isomorphism lemma, or underived/derived exchange lemma duplicates the existing DAG. The two component facts are existing statements, not newly renamed clauses of the assigned theorem. Their hypotheses are genuinely weaker categorical conclusions: monicity and existence of a section, respectively. The cancellation, uniqueness and naturality calculations remain in this item's steps.

## Mathlib searches

I read the seven logged results. Both geometric LeanFinder phrasings returned open-immersion inverse-component identities and Scheme.Modules.restrictFunctorIsoPullback / pullback composition results. These concern structure-sheaf modules on Zariski spaces, not the pro-etale condensed-coefficient derived categories in the theorem. The first geometric grep returned no hits; the broader extension-by-zero grep returned only the unrelated multiplicative-character result. Loogle and LeanSearch found CategoryTheory.NatTrans.isIso_iff_isIso_app and generic categorical facts. These support the elementary assembly, but do not provide the geometric inputs in one line and hence do not make this item a Mathlib leaf. All searches succeeded; none is misreported as unavailable or as an exact match. No search was invented or repeated.

## Review by NH

I checked the statement against the current blueprint theorem and its unit, and against the upstream-master declaration and its explicit exchange definition. The arrows are X' to X above Z' to Z, with j and j' vertical open immersions; the map is j'_! Lg'^* to Lg^* j_!, with the same square comparison and the same unit and counit. The coefficient remains an arbitrary commutative condensed ring. I made no identification with ordinary etale sheaves, finite coefficients, or structure-sheaf modules. The positive-characteristic finite-type setting is already part of the cited exchange definition's setting and unit; it is not an added assumption.

For step 1 I opened the entire statement of stage3-sfb-open-base-change-component-mono. It explicitly assumes exactly that setting, a cartesian square, both open immersions, and equality of the natural transformation with the explicit exchange formula, and concludes monicity of every component. I use that formula itself, so the equality hypothesis is reflexivity. I also opened the exchange definition and copied its formula into citations.json. The step does not take any geometric assertion from the definition.

For step 2 I opened the entire statement of stage3-sfb-open-base-change-component-section. It supplies a map from the target of each component back to its source, whose diagrammatic composite beta then alpha is the identity on the target; it explicitly supplies no naturality. The step converts that equation to ordinary composition, then writes the monic-cancellation calculation giving the other inverse equation and the uniqueness calculation. Thus it uses exactly the cited existence conclusion and the monicity proved in step 1. It never uses an internal helper from either component lemma's proof.

For step 3 the only inputs are the preceding inverse equations and naturality of the specified exchange. Multiplying the naturality equation by the two inverses gives the displayed naturality equation for beta. The two natural-transformation composites are identities componentwise. This is an elementary calculation, written in full; no separate Mathlib or geometric lemma is hidden in it. Each step is below 2000 characters.

I checked the small cases: identity open immersions give identity components under the canonical unitors; an empty open gives the unique map between zero extensions, and the cancellation equations remain valid; a base-change map landing in the complement has empty X' and both functor values zero. No nonemptiness, coefficient finiteness, properness, density or arbitrary chosen inverse's naturality is required. I also checked the necessity of the two categorical inputs: a section alone does not imply an isomorphism (a split projection need not be monic), and monicity alone does not produce an inverse. Both existing statements are used.

Against delivery-errors B–E: no new unsplit statement or definition is introduced, no proof is hidden in a new statement, and no Mathlib leaf is asserted from a merely similar result. All non-elementary steps cite existing statements with verbatim quotes; the generic algebra is explicit. The cyclic dependencies are removed, the route stays in the same unit, and the item is genuinely assembled rather than passed to a new equivalent lemma. No statement, source, chapter, unit or audit field was silently changed.

## Repair of the returned landing refusal

The return identified one issue: the statement of def-sfb-dc-open-base-change-morphism changed after the approved reading. I retained the delivered split, all seven logged searches and their recorded results, and the earlier review. The initial required dry run on the retained work exited successfully with OK (not pushed), commit 69ef760112, but that alone would not repair the stale-citation return.

I compared the retained item with the current shared item: the differences remain the proof, proof dependencies/origin, Mathlib searches, blueprint.same_as, status and split_report. The theorem statement, source, chapter, unit, import and maintainer audit fields agree with the current item. The delivery command constructs its commit on the current server DAG, so no shared checkout or git operation is needed here.

I re-read the entire current statement of the changed definition, the current statements of both component lemmas, their dependencies, the current unit and chapter, and the original main-20261015 definition and theorem files. The updated definition makes explicit the original setting, endpoints, component formula and composition comparison, and cites det-def-sfb-base-change-morphism-comparison instead of the larger pushforward base-change construction. Substituting top jprime, left gprime, right g, bottom j into that comparison gives c_(jprime,g) after c_(gprime,j)^(-1), in precisely the orientation required by the component lemmas. The square equation is j composed with gprime = g composed with jprime. Neither the comparison nor this exchange needs pushforwards to preserve the bounded constructible category. The arbitrary condensed coefficient category is unchanged.

Step 1 now spells out this exact component and comparison, rather than relying on the earlier definition's abbreviated wording. The equality premise in each component statement is still reflexivity for the specified exchange, with the usual associators/unitors understood in the functor composites. I replaced the definition quotation in citations.json with its newly explicit component formula and verified all three quotes verbatim against the current statements. Steps 2 and 3 still use exactly the section equation, monic cancellation and the written naturality calculation; neither imports any helper from a cited proof. Both component statements retain their full common field/scheme/coefficient hypotheses and the exact monicity/section conclusions used here. No new dependency or node is necessary.

## Review by NH — repair revalidation

For the returned issue I checked the changed definition against the blueprint unit and its original displayed unit-comparison-counit composite, and read the comparison-only node to check the swapped-square orientation. I also read upstream-master MorphismDefs.lean:85–182: its squareTransport uses sq.flip, and its unit/counit whiskerings give the same component as step 1. Its isomorphism theorem still ends in sorry; the slopmaster2 search for the blueprint tag and the full bounded-constructible exchange name gives no hit. There is no new attachment. This repair does not change the mathematical statement or its route.

I rechecked C4 separately for each cited statement: the current definition supplies exactly the new step-1 formula; component-mono supplies monicity for that formula under the setting and cartesian/open hypotheses; component-section supplies the right inverse on its target under the same hypotheses. The cancellation and naturality calculations remain explicit, so C1 adds no missing geometric input. Identity opens, empty opens and zero coefficients still satisfy all equations. No new statement needs a duplicate or Mathlib search; the seven retained searches answer the unchanged theorem question. Each repaired step remains below 2000 characters. The final dry run is rerun after these edits and must exit before the push.

## Unfinished work

None in the assigned one-level split. The two reused component nodes remain existing DAG dependencies and are outside this item's editing scope. Server dry run and direct push follow this report; the final delivery command records their result.
