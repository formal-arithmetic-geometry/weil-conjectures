# Stage-1 report: sk-def-sfb-filtered-two-colimit

## Files written

- dag/nodes/sec-six-functors-basics/sk-def-sfb-filtered-two-colimit.json — existing definition, split; statement unchanged; no exact Mathlib match.
- citations.json — complete verbatim statements supporting each node citation in each step.
- report.md — this report. searches.jsonl was written only by msearch.py.

New nodes: 0. New Mathlib leaves: 0. Reused the existing cocone, conditions, model and characterization nodes rather than recreating their statements.

## Attachments

None. Searches by the item id, CategoryCocone, EssSurjObj, HomSurj, HomInj and filtered-colimit concepts in the project Lean source found no slopmaster2 declaration for this definition. The upstream master reference has CategoryTheory.CategoryCocone (line 63), CategoryTheory.CategoryCocone.EssSurjObj (77), HomSurj (83), HomInj (90), IsFilteredTwoColimit (97), IsFilteredTwoColimit.exists_iso (104), and IsFilteredTwoColimit.exists_map_eq (111), in WeilConjectures/CategoryTheory/FilteredTwoColimit.lean. These were read to check intended notation and all clauses, not claimed as finished slopmaster2 attachments. The reference file's definitions match the item, including the absence of coherence and the fact that only Preorder I is assumed.

## Wanted sources

None. The main-20261015 blueprint definition and all four existing detail-node sources are available locally. No Stacks assertion is needed for defining this particular predicate or projecting its fields, so no Stacks tag or unrelated external theorem is introduced. No SGA source is used.

## Corrections and scope

The main definition and all its hypotheses are preserved verbatim. Its imported stmt_deps were empty although its two constituent notions already had blueprint nodes. Added det-def-sfb-filtered-two-colimit-cocone and det-def-sfb-filtered-two-colimit-conditions. The latter states the same predicate, on the data of the former, and is therefore recorded in blueprint.same_as. This is reuse of existing material, not new clause nodes.

The imported proof's second paragraph used a comparison-category construction without citing a construction or characterization node, and did not spell out normalization. The blueprint already has both nodes. Step 3 now states their directed, coherent, normalized hypotheses expressly and cites the construction and the equivalence result. No normalization theorem is silently used and no such hypothesis is imposed on the item's definition. This step is an additional interpretation, not an unconditional assertion that arbitrary incoherent data have a categorical universal property. The source _section.md itself states just the definition and its two immediate consequences.

The current imported node has no chapter or unit metadata, and dag/chapters/sec-six-functors-basics.json and dag/units/sk-def-sfb-filtered-two-colimit.json do not exist. I read the actual current chapter and unit blueprint _section.md files instead. Their prescribed coefficient-category route is unchanged; no unit file was created or maintainer metadata altered. The chapter's broader references are not citations for any hidden categorical theorem here.

## What remains unfinished

No part of this one-level split remains. Existing dependency nodes keep their own statuses and are not edited by this delivery. The optional characterization is cited as a statement under all of its hypotheses; proving or splitting its construction is that node's task.

## Not duplicates

No new nodes were created. Whole-DAG searches for 2-colimit, two-colimit and CategoryCocone, and blueprint_refs.py searches for 'filtered 2-colimit' and 'cocone of categories', found the four existing detail nodes. They are all reused. The constructible-cocone two-colimit theorem is an application with coefficient hypotheses, not another general definition.

## Review by Q63

I read the current main-20261015 chapter _section.md, the item's _section.md, and the cocone and conditions detail files against their DAG statements. I also opened the model and characterization DAG statements and their displayed arguments before using them. The definition intentionally makes sense for any preorder; I have not inferred directedness from its name. Its Hom-surj formula composes the inverse source comparison, the image of the stage morphism, and the target comparison in that order, with all intermediate objects checked.

For step 1, the cocone node supplies exactly the three sorts of data and explicitly says no compatibility is part of them. The conditions node supplies exactly the three predicates with the same quantifiers and the same comparison maps. No theorem about a categorical colimit is taken from either definition. Checking the displayed composite's endpoints is elementary from those data. For step 2, (Obj) is instantiated at an arbitrary object d and (Hom-inj) at arbitrary equal-image parallel morphisms at k; their existential witnesses are precisely what the two concluding assertions require. No finite-presentation theorem, choice of common upper bound or general colimit result is being hidden in these projections.

For step 3, I checked that the model node assumes directedness and the full normalized coherent structure (including compatibility of theta), and supplies not only a formula but a well-defined category and comparison functor. The characterization node explicitly gives all three equivalences and the final equivalence of categories. Thus those two citations say exactly what the step takes from them. This does not use the incorrect shortcut of applying the characterization to arbitrary incoherent cocone data. The reference to the model is to its statement, not to construction details available only inside its proof. Every citation has its whole statement copied verbatim in citations.json; all four dependency nodes were opened and checked for these clauses.

I tested small cases: with empty I the object condition forces D to have no objects and the other clauses are vacuous; no nonempty index is silently assumed. For a singleton I with identity transition, Phi the identity and theta the identity, all three conditions hold by direct witnesses. For a constant terminal stage category mapping into a discrete category with two objects, (Obj) fails, so the final assertion is correctly conditional. For arbitrary, nonnormalized singleton transition data the predicate remains well typed; the comparison-model interpretation is deliberately not applied. Parallel morphisms g=g' satisfy Hom-inj already at k by reflexivity of the preorder and equality under any functor; distinct equal-image arrows still require the specified eventual equality. These checks required no statement repair.

I checked delivery-errors B–E against the actual files: no new unsplit nodes, duplicated claims, missing definition references, source-tag substitutions, or unchecked Mathlib leaves; all citations are supported by node statements; all non-elementary content of the optional interpretation has cited nodes; the final projections are elementary. Dependencies lead only to the four pre-existing nodes (conditions and model lead to cocone, characterization to conditions/model), and none leads back to the item, so these edges introduce no cycle. The seven Mathlib queries in the item were really run through msearch.py, with two semantic phrasings, two Loogle queries and two source patterns, plus LeanSearch. I read the returned hits and inspected the plausible candidates in Mathlib: Types.FilteredColimit.isColimitOf/isColimitOf' concern Type-valued diagrams, IsFinitelyPresentable.exists_eq_of_isColimit requires finitely presentable objects of one category, Functor.final_iff_of_isFiltered concerns finality of one functor, JointlyFaithful has a common source and no eventual equality, and Pseudofunctor includes coherent composition/unit constraints. None is an exact or one-line replacement for this ordinary-category predicate without coherence. The existing statements, proof_origin, import flags and blueprint fields were checked; only split-owned fields were changed.

## Validation

The required deliver.py --no-push dry run is invoked after writing this report. Its final output is retained in dry-run.log in the sandbox. Nothing is pushed by the first worker.


## Second reading by Q63

- Item statement: checked every quantifier, preorder hypothesis, functor/isomorphism direction and all three conditions against main-20261015 `sk-def-sfb-filtered-two-colimit/_section.md`; exact agreement. Read the archived master `FilteredTwoColimit.lean` declarations 63–115 as notation reference only; the object-isomorphism direction differs only by inversion. Independent slopmaster2 name searches found no declaration to attach.
- Step 1: read the complete statements and blueprint source files of `det-def-sfb-filtered-two-colimit-cocone` and `det-def-sfb-filtered-two-colimit-conditions`; they supply precisely the data and predicates used. Checked the three arrows in the Hom-surj composite in order, from the source comparison inverse to the target comparison. This is an elementary definition/type check, not a categorical universal-property claim; PASS (C1–C4, E1).
- Step 2: checked against (Obj) and (Hom-inj) of the conditions node and the source's final paragraph; fixing the quantified object or pair of equal-image arrows and taking the supplied witnesses gives exactly the two conclusions in two lines. No directedness, nonemptiness, or coherence is used; PASS (C2–C4, E1, E5).
- Step 3: opened the complete model and characterization node statements and their main-20261015 source files. The model supplies the well-defined category and comparison functor under directedness, normalization, the tau cocycle and compatibility of theta; the characterization states each of the three equivalences and their combined equivalence. The step assumes exactly this additional structure and draws only these conclusions. No normalization theorem, construction hidden inside a cited proof, or unconditional interpretation of incoherent data is used; PASS (C1–C4, E1, E5).
- New nodes: none; no elementary auxiliary, duplicate, clause restatement, unsplit statement or Mathlib leaf is introduced. B1–B8 therefore require no new-node repairs. Whole-DAG searches by `filtered 2-colimit`, `two-colimit` and `CategoryCocone` confirm that the four dependencies are existing blueprint nodes; each source was read, not inferred from its id.
- Existing cocone dependency: checked the preorder, all three sorts of data, absence of coherence, and component endpoints against its source; PASS.
- Existing conditions dependency: checked Obj, both independent indices in Hom-surj, both upper-bound requirements, the composite, and the eventual equality in Hom-inj against its source; PASS.
- Existing model dependency: checked all extra coherence/normalization hypotheses and its explicit comparison functor conclusion against its source; these are exactly what step 3 cites; PASS.
- Existing characterization dependency: checked clauses 1–3 and the final equivalence against its source and the model hypotheses; step 3 uses its statement without appealing to its proof; PASS.

Small cases: for empty I, Obj holds precisely when D has no objects, and both Hom conditions are vacuous. For singleton I with identity transitions and comparisons, an identity vertex functor satisfies all conditions; a terminal stage mapping to one object of a discrete two-object vertex fails Obj. For the nondirected two-element discrete preorder with all stages and D empty, every condition holds vacuously, confirming that directedness cannot be inferred from the definition. Equality g = g' satisfies Hom-inj using k' = k and functorial preservation of equality, even without normalized transitions. The source's “finite stage” means one index, not a finite category. No field, scheme or integer parameter occurs, so those edge cases do not apply. No statement dispute was found.

I rechecked all five entries of citations.json against the complete current dependency statements; each is verbatim and attached to the correct step. Read GOAL.md and coord/dag-sync.md; no Lean, live file, compiler, chapter route or maintainer metadata was changed. No Stacks claim or forbidden SGA route is used.

Changes and reasons: preserved the worker's correct statement, proof, dependencies and first review. Added this independent second reading and three genuinely executed Mathlib searches with different phrasings (LeanFinder, grep, Loogle), recording their actual results in the item's mathlib_searches and searches.jsonl. The returned ordinary-cocone declarations concern a diagram in one category; Mathlib EssentialImage.lean's Functor.EssSurj concerns one functor; ReflectsIso/Jointly.lean lines 46–49 give same-source joint faithfulness with immediate equality. None supplies the varying-stage, eventual-equality predicate without coherence, so no leaf was added. No new nodes or citation edits were necessary.

The delivery tool's installed usage accepts only group, item and optional --no-push; the trailing dot in the brief prints usage without validation. The required validation and delivery use those installed arguments, with no tool modification.
