# Stage-1 report: def-nagata-immersion-shrink-to-closed

## Files written

- dag/nodes/sec-nagata-compactification/def-nagata-immersion-shrink-to-closed.json: definition; split; no exact Mathlib match. The definition and its one statement dependency are retained unchanged. Filled blueprint.same_as, recorded six actual searches, and added split_report.
- citations.json: empty list, because this is a definition with no proof steps.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

No ATTACH request is made, as the brief explicitly prohibits repeating the rejected attachment. The current read clone now does contain AlgebraicGeometry.Scheme.Hom.closedShrink at lean/WeilConjectures/AlgebraicGeometry/FinitePresentationModel.lean:53, and toClosedShrink at line 58. The former chooses the open; the latter chooses its factorization morphism. This differs from the earlier worker's reported source state. I read the bodies, but did not run a compiler or certify their transitive axiom closure. The existence theorem alone is not the chosen-object definition. This delivery completes the requested definition dependency split.

## Literature wanted

None. No WANTED entries.

## Issues and corrections

The item is a definition, not a theorem with an existence proof to split. Its imported dependency is already the correct immediate constituent: lemma-nagata-immersion-shrink-to-closed-exists. Its statement is unchanged, including the choice of an arbitrary witness. Added no artificial choice lemma, no duplicate existence node, and no proof of the neighbouring properties theorem. The source's bypass note is retained as required, even though the current read clone now has explicit definitions. No statement dispute and no route departure.

## Unfinished work

No mathematical work remains on this definition-only split. Its existing existence-theorem dependency is a separate item and is not edited here. Independent review and landing belong to the maintainer.

## Not duplicates

No new nodes. Blueprint searches for immersion-shrink-to-closed and closedShrink distinguish this definition from the separate existence theorem and the properties theorem. No other imported blueprint node found states this chosen-object definition in another form; same_as is []. The broad choice search also found no equivalent definition. Whole-DAG keyword searches were read alongside these blueprint results.

## Review by Q118

I read the current main-20261015 definition source at literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-fp-models/def-nagata-immersion-shrink-to-closed.md, its preceding existence node in the same source directory, the DAG statements of the existence and properties nodes, and the chapter and unit records. The unit's first paragraph explicitly calls for shrinking the immersion to a quasi-compact open where it is closed. This definition names that open and does not replace the finite-presentation-model route.

There are no proof steps or new nodes requiring step citations. I checked the only statement dependency word for word: it assumes an immersion i:X→Y with X quasi-compact, and supplies a quasi-compact open W containing i(X) with induced map X→W a closed immersion. Those are exactly the hypotheses and witness referred to by the retained definition. No quasi-separatedness, Noetherianity, affine target, or finite-presentation hypothesis is added. Choice is made once for each immersion; neither uniqueness nor naturality nor a smallest open is asserted. The properties of the choice belong to the separate existing lemma-nagata-immersion-shrink-to-closed node, which this definition does not cite, so no circular dependence is introduced.

For the non-hollow-definition check, I read the actual current witness theorem AlgebraicGeometry.Scheme.Hom.exists_isCompact_isClosedImmersion in lean/WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:117-148. Its body contains an explicit finite affine-subcover construction, not sorry. Thus the named selection is from an existing proved witness theorem, rather than invented data selected from an unproved arbitrary existence assertion. I also read the current closedShrink and toClosedShrink bodies at FinitePresentationModel.lean:53-59. No Lean was written or compiled. This is source inspection, not a claim to have performed the attachment closure audit.

I read the actual results of all six logged msearch commands: LeanFinder twice, Loogle, LeanSearch, and grep twice. The nearest Mathlib object is coborderRange (Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:56) with liftCoborder (line 64) and its closed-immersion instance (line 90). Its definition only chooses the largest open where the image is closed; it does not supply a quasi-compact open. For example, for the empty immersion into an infinite disjoint union of nonempty affine schemes, the largest such open is the entire non-quasi-compact target, whereas the empty open is an admissible quasi-compact witness. Hence these hits do not identify the item's particular construction. The reversed open-then-closed factorization for quasi-compact morphisms also does not do so.

I tested empty source (the empty open is a permissible witness), the identity of a quasi-compact scheme (the image forces the chosen open to be the whole scheme), a quasi-compact open immersion, and closed immersions into non-quasi-compact targets (one still needs the finite-subcover witness, not the whole target). Multiple admissible witnesses are permitted by the source. Nothing in the definition treats image containment alone as a general subscheme factorization theorem; the needed closed immersion is part of the existence witness.

Against delivery-errors B–E, this introduces no new statement, no hidden lemma, no copied clause, and no omitted non-elementary proof step; the existence theorem remains explicitly named. All original metadata, import_flags, and blueprint_update are preserved. The six mathlib_searches are taken from the actual searches.jsonl records with their exact query strings. There are no long proof steps or off-unit proof citations. The only changes are the definition split status and its search/review provenance.
