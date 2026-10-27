# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-open-boundary-codimension-one.json: statement, split in four steps; no Mathlib match found.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-punctured-local-dimension.json: one new statement-only unsplit local algebra lemma (Stacks 0BCR); no Mathlib match found.
- citations.json contains verbatim statement excerpts for every step/node citation. searches.jsonl preserves the actual search-tool output records.

## Attachments

None. I searched the live WeilConjectures source for the item id and for affine complements, punctured spectra, boundary codimension and local dimension. No declaration states this item exactly with a completed proof. Modules/AffineComplement concerns affine complements of sections of ample lines, not this dimension bound. Sorry declarations are not attachments.

## WANTED

None. All used source passages are present in literature/stacks-project/.

## Corrections and scope

The item's statement is unchanged and is exactly the dense-open clause of divisors Tag 0BCV, lemma-complement-affine-open. Its old proof was empty. No statement dispute arose. The proof now expands Tag 0BCU rather than introducing a new node that would merely restate the item for affine open immersions. The only new node is the local algebra implication from Tag 0BCR; it has neither proof steps nor a hidden proof sketch in its statement.

I read the chapter and unit records and latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This remote descendant is a local geometric prerequisite in the already-recorded Cartier-boundary/ample-line route. It is not the unit's key theorem; no unit record is changed. blueprint_refs.py ancestor prints None for the item, consistently with the inherited from.node=null. I retained that recorded ancestry and its via list, adding the item at the front of the new node's via. The exact supporting place is filled, and same_as is empty after searching the full DAG, blueprint index and latest blueprint text.

## Searches and new-node rationale

Mathlib searches were run exclusively through msearch.py, with LeanSearch, Loogle, LeanFinder and grep. I read the returned hits and tried a second semantic phrasing of the local algebra lemma and the item. The local-ring hits give finite dimension, dimension-zero spectra, definitions of dimension at most one or DVR/Dedekind characterizations. None gives the bound from affine punctured spectrum. The generic-point hits have no affine-boundary hypothesis or conclusion. The actual tool/query pairs are preserved exactly in mathlib_searches and searches.jsonl; inherited searches on the item are also retained.

Before creating the new node I searched the DAG for 0BCR, punctured/affine/dimension formulations and the proposed id, used blueprint_refs.py search for '0BCR', 'affine punctured', 'affine punctured local' and 'punctured spectrum', and searched the latest blueprint. No matching node exists. The blueprint's lem-exc-punctured-curve-branches assumes an excellent reduced one-dimensional strictly henselian local ring and describes its generic branches; it does not infer dimension from affineness. The new node is not a clause of the item: it concerns arbitrary Noetherian local rings, assumes affineness of their punctures, and has no dense affine open or global boundary component. Steps 1–2 construct the particular local ring and identify its puncture; Step 4 supplies the strict positive dimension that 0BCR does not give.

## Not duplicates

No pre-existing node cites Tag 0BCR. lem-sfb-affine-punctured-local-dimension vs lem-exc-punctured-curve-branches: the latter assumes dimension one and describes branches of a strictly henselian excellent reduced ring; the new lemma proves an upper dimension bound from affine puncture without those extra hypotheses.

## Review by NI

I read divisors.tex Tags 0BCV and 0BCU in full, and Tag 0BCR including its length/snake-lemma proof and its following Hartogs remark. I also read schemes.tex Tag 01J7 and checked the tag/label map. The new node states only the only-if implication of 0BCR, so its proof remains future work at the next DAG level. Its Noetherian and local hypotheses are explicit, including the unique maximal ideal; affineness and spectrum/dimension conventions have their definition-node citations.

Step 1 uses the actual statement of the affine-source/separated-target leaf for j, not just a definition of an affine morphism. The source is affine and X is separated exactly as required. The scheme definition supplies affine charts; pqf-lem-affine-open-locnoeth gives R Noetherian; affine-open-stalk-localization clause (c) identifies the supplied A with R localized at the prime, and localization-noetherian then gives A Noetherian. I checked those statements, rather than citing the finite generation of a stalk's maximal ideal as if it asserted stalk Noetherianity.

Step 2 uses spec-local-ring-canonical-morphism for the local chart description, closed point and image of c, and localization-spectrum-embedding for injectivity. The generic-point uniqueness statement of scheme-sober supplies precisely the equality inference after maximality of Z gives equal closures. If a generalization y of xi remains in the boundary, its closure contains Z and is irreducible in that boundary, so maximality forces the same component. This proves the inverse image is the single closed point, rather than assuming that boundary generic points have no other generalizations. The inverse image of the open immersion has the restricted structure sheaf, yielding equality with the punctured open as schemes. This is an explicit elementary identification from the cited statements, not a new black-box comparison lemma. The only off-unit non-leaf tool is the canonical-local-spectrum node; its tool use is declared in split_report.

Step 3 uses clauses (1) and (2) of affine-morphism-permanence, which explicitly give arbitrary base change and affineness of a source over an affine target. It applies the new 0BCR node only after A is Noetherian local and its puncture is affine. All three hypotheses were checked in the earlier steps. This produces only the upper bound.

Step 4 uses open preservation of local Noetherianity in pqf-def-locnoeth, affine-scheme-qcqs for quasi-compactness, noetherian-finitely-many-components for finiteness, scheme-sober for component generic points, and stalk-dimension-generalization-chains for the final lower bound. I wrote the finite-component density argument explicitly: removing all other components leaves a nonempty open lying in the chosen component, so a dense open meets each component and therefore contains its generic point. It supplies a strict generalization of xi, since xi is outside U. Local Noetherianity suffices because this argument is made on one affine chart; no global Noetherian or quasi-compact hypothesis was added to X. I corrected the first draft to cite affine-scheme-qcqs explicitly rather than silently use affine quasi-compactness.

I checked delivery-errors B–E: the new statement is self-contained, statement-only and uses single TeX escaping; every cited node is live and unmerged and each citation has a verbatim excerpt. The split does not transfer the conclusion to a renamed child. Every non-elementary input is cited, and the elementary steps write out their arguments. No step exceeds 2000 characters. I checked the empty boundary U=X, dimension-zero local rings (the puncture can be empty and affine), a DVR (a one-point generic puncture and dimension one), a two-dimensional local polynomial ring (its puncture is not affine by 0BCR), and reducible/nonreduced schemes: neither integrality nor normality is used. Density is necessary for equality: U empty in a point scheme would yield a dimension-zero boundary, while the new local lemma correctly permits dimension zero. No SGA source or alternate purity route is used.

## Unfinished work

None at this splitting level. The one new statement-only node is deliberately unsplit for the next worker. The required server dry run and push are recorded below when completed.
