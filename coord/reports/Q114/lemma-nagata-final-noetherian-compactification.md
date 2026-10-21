## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-final-noetherian-compactification.json`: statement, split into four steps; no Mathlib match for the item.
- `citations.json`: one verbatim statement excerpt for every step/dependency pair.
- `report.md`: this report. `searches.jsonl` is the search command's own record.

New nodes: 0. Mathlib leaves added: 0. No unit record is changed: this is an intermediate lemma, not the unit's key statement.

## Attachments

None proposed. The task expressly requires a split after rejection of the earlier attachment. In the currently supplied source, `WeilConjectures/Compactification/FinitePresentation.lean:232-244` now contains the tagged definition `AlgebraicGeometry.descendedModelCompactification` and the tagged property theorem `AlgebraicGeometry.descendedModelCompactification_spec`. I read these, together with the Noetherian recursive construction and theorem in `Noetherian.lean:205-263`, as reference material. I do not infer that the prior attachment was valid in its supplied source, or use an upstream existence statement to identify the chosen DAG construction. The split proves that identification directly from its definition.

## WANTED

None. All sources used are present.

## Corrections and observations

The item's statement is unchanged and is meaningful through `def-nagata-final-noetherian-compactification`. There is no statement dispute. The imported proof omitted its use of `lemma-nagata-final-descended-model` from the step's `uses` even though it already listed it in `proof_deps`; it also left the finite-type implication and identification with the selected object implicit. The four steps make those arguments explicit and set `proof_deps` to their exact union. The compactification definition is now an explicit statement dependency.

I followed the current `main-20261015` blueprint update, not a replacement existence route. The current Noetherian theorem's blueprint statement explicitly supplies the hypotheses (Noetherian base, separated finite-type morphism) as well as correctness of the recursive construction. The old DAG statement already gives the latter conclusion, and its construction definition supplies the ambient hypotheses. I read both versions and do not take merely compactifiability as a certificate for an arbitrarily chosen candidate.

## Searches

All seven searches in the item were run through the prescribed `msearch.py Q114 lemma-nagata-final-noetherian-compactification` command, and their actual results are in `searches.jsonl`. Two semantic phrasings found properness and Noetherian compactness results but no Nagata compactification declaration in Mathlib; two Mathlib grep patterns confirmed this. The first Loogle query reported an unknown identifier for the project-specific `AlgebraicGeometry.Compactification`; this is recorded as the actual query failure, and is not used alone as an absence argument. A second Loogle query found the auxiliary implication `instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`. I read the finite-presentation class in `Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean` and the properness material returned by the semantic search. Neither supplies the item's selected construction. The affine-algebra argument for the auxiliary implication is elementary and is written in step 2, not made into a new node.

I searched the whole DAG and the blueprint index for finite presentation, Noetherian compactification, and compactification of a morphism, as well as the source for the item's tag and selected-object names. The existing Noetherian theorem already states exactly the general recursive-construction result needed here. Its specialization and the defining equality require no new lemma.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs. The general `thm-nagata-noetherian` is cited rather than copied into a specialized node. The other final compactification lemma is about the subsequent base change to the original base, whereas this item certifies the selected factorization over the Noetherian stage.

## Review by Q114

I read the stage-1 brief, the stage document, the three blueprint levels in SETUP, GOAL, the chapter and unit records, and both occurrences of delivery-errors B through E. For the item I read the statement and proof at `literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-cor-nagata-sketch-fp/lemma-nagata-final-noetherian-compactification{,.proof}.md`, together with the selected-final-compactification definition in that unit. For the theorem used in step 3 I read `sk-thm-nagata-sketch-noetherian/thm-nagata-noetherian{,.proof}.md` and the definition of the recursive construction. There are no new nodes needing separate sources. The auxiliary implication was checked against Stacks `morphisms.tex`, label `lemma-finite-presentation-finite-type`, Tag 01TW, and its preceding definition `definition-finite-presentation`, Tag 01TP. The complete affine-algebra argument, rather than the omitted proof in Stacks, is written in step 2; the proof origin is therefore agent, following the blueprint.

For step 1 I opened `lemma-nagata-final-descended-model` and verified that its statement explicitly says the selected morphism is separated and of finite presentation and its base is Noetherian. These are exactly the three properties taken from it. I also read `def-nagata-final-descended-model`: its directed presentation and retained gluing data select the model in question; no assertion about an arbitrary model is substituted, and no comparison isomorphism or descent theorem is needed afresh here.

For step 2 I opened `def-sbc-locally-finite-presentation` and `def-weil-finite-type-morphism`. The first explicitly gives the finite polynomial-quotient chart description and says finite presentation includes quasi-compactness. The second defines finite type as local finite type plus quasi-compactness. Images of the finitely many polynomial variables generate the quotient, so forgetting finite relations gives the required local finite type property, while quasi-compactness is retained. This is a two-line elementary implication, not a theorem smuggled in under a definition. It does not claim that local finite presentation alone implies finite type. All coefficient rings are arbitrary commutative rings; no field or Noetherian algebra assumption is used in this elementary step.

For step 3 I opened `thm-nagata-noetherian` and checked that its statement certifies the recursively constructed factorization itself. Its current blueprint supplies the full hypotheses: step 1 gives Noetherianity of the target and separatedness, and step 2 gives finite type of the very same morphism. This keeps the unit's prescribed descent/Noetherian-compactification/base-change route, and uses the Noetherian unit already named in the unit record. There is no off-route tool use.

For step 4 I opened `def-nagata-final-noetherian-compactification` and copied its displayed equality into the citation: the selected object is literally the recursive construction at this selected model. Substitution in step 3 is the whole identification; no uniqueness of compactifications is asserted or needed. I also opened `def-nagata-compactification`, whose statement includes the factorization equation, quasi-compact open immersion and proper morphism. Step 3 already gives a compactification in that sense; step 4 simply spells out these fields, so even the stronger quasi-compact-open-immersion convention of the current DAG is retained. The current blueprint's omission of the word quasi-compact in its general definition causes no weakening here: the recursive construction gives the DAG compactification property used by the theorem.

I checked B1-B9: no new unsplit node carries a hidden proof, all objects are introduced through the named selected-object definition, the formulas use ordinary single TeX escaping after JSON decoding, sources and exact searches are recorded, and the blueprint search gives no second blueprint node with the same selected-stage statement (`same_as: []`). For B10 I obeyed the task's explicit instruction to split rather than resubmit the rejected attachment; the reference source inspection above is recorded transparently. For C1-C5 every non-elementary operation is a cited statement, the only elementary steps are the explicit quotient-generator implication and substitution of a defining equality, and `citations.json` quotes the statements, not their proofs. For C6-C8 the existing theorem is in the unit's stated route, no new dependency is introduced from the item back to itself, and no tool-use exception is requested. D1-D5 are met by writing the actual argument with existing general results rather than restating the conclusion in a new node.

For E1-E6 I checked each theorem hypothesis and the identity of its base, source and structure map. Empty selected source and empty base cause no problem: finite-presentation/quasi-compactness statements remain valid and the recursive Noetherian construction includes its empty stage. An affine identity morphism over a Noetherian base is also covered without changing the selected construction or claiming it equals some other compactification. Finitely presented algebras with zero variables, zero relations, or the zero ring still have the asserted finite generating set (possibly empty). No density, nonemptiness, integrality, or smoothness hypothesis was added. No E7 source error was found. All four steps are below 2000 characters and none hides a long comparison argument.

## Unfinished work

None in the requested one-level split. The existing theorem and definition remain their owners' items; this delivery adds no replacement nodes. Delivery checks are run by the prescribed remote dry run, with no local DAG-check tool or Lean compiler invoked.
