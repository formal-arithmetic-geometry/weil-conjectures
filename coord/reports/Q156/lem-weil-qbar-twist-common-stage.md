# Q156: lem-weil-qbar-twist-common-stage

## Files written

- dag/nodes/sec-smooth-purity/lem-weil-qbar-twist-common-stage.json — statement split in seven steps; statement unchanged; not a Mathlib leaf. Zero new nodes and zero Mathlib leaves.
- citations.json — eleven verbatim statement excerpts, one for each step/dependency pair.
- report.md — this report. searches.jsonl contains the six actual searches made in this attempt. write_split.py is a sandbox-only preparation script, not a delivery node.

## Attachments

None. Searches of the whole read-only slopmaster2 WeilConjectures source for the exact item id and for qbar/twist/common-stage concepts found no declaration giving this statement. Existing finite torsion Tate-twist declarations do not assert descent to this raw common-stage rational coefficient category. No master sorry declaration was treated as finished evidence.

## WANTED

None. The relevant blueprint sources and all input-node statements are available locally.

## Findings and changes

The item had no proof. Its statement already carefully assumes finite-stage functors, their two natural inverse identities, natural scalar comparisons, tower coherence, and evaluation compatibility. Those assumptions make the remaining task a direct categorical calculation. In particular, it would be a relabelling to create a new lemma saying that compatible twist functors descend. Instead the item itself now carries that argument.

I retained the statement, all original statement dependencies, all previous searches, source ancestry, and metadata. I added six genuine logged searches (LeanSearch, two LeanFinder phrasings, two Loogle queries, and grep). The first Loogle query was rejected for an unknown identifier and is recorded as such; the second valid query gives ordinary colimit changes of indexing category, not a filtered two-colimit of coefficient categories. LeanFinder gives type-colimit relations and ordinary scalar-extension pseudofunctors, and LeanSearch gives ordinary module, shift and derived-functor comparisons. Grep found filtered-colimit infrastructure, not twist descent. I read the relevant Mathlib type-colimit/ordinary colimit descriptions and the source of IsLimit's whisker-equivalence constructions, FilteredColimitCommutesFiniteLimit, and Indization/FilteredColimits. None is a one-line specialization giving the whole item.

The current blueprint relocated prop-weil-twist-preserves to sec-six-functors-basics/sk-prop-sf-existence, separating statement and proof files. I read both current files and the older master node. The final sentence still gives the same common-finite-stage route. The item's historical chapter, unit and blueprint ancestor remain untouched; the proof points to the current proof source. The owning unit record concerns exceptional adjoints, while this imported subsidiary node supplies a coefficient tool for prop-weil-twist-preserves; it is not the unit key statement, so no realized fields were changed. I also read the slopmaster2 note 42_qbarl_triangulated_colimit.tex for its transition datum, but did not import its extra Karoubi completion or its finite-stage hypotheses into this proof.

The only off-unit statement used as a generic tool is lem-weil-scalar-extension-composition, recorded in split_report.tool_uses. Its canonical associator identifies endpoints in the Hom transport, without replacing any exceptional-adjoint or purity argument.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to compare. Whole-DAG and blueprint searches for common-stage twists and twist functors found the parent prop-weil-twist-preserves, the coefficient/twist definitions and lem-wf-tate-twist-compatibility. The last concerns roots-of-unity pullback and finite scalar extension for Weil sheaves; it does not supply representative independence or inverse natural isomorphisms for this common-stage category. The parent depends on this item and was not cited in its proof, avoiding a cycle.

## Review by Q156

I reviewed delivery-errors B–E against the written node and the following actual statements, rather than relying on their titles. The source for the item is the final sentence of the current prop-weil-twist-preserves.proof.md, checked against the master version. There are no new-node sources to review. The proof is marked agent-written because the blueprint omits this categorical calculation.

Step 1 uses lem-weil-scalar-extension-composition for a canonical natural scalar associator compatible with identity extension, lem-weil-integral-twist-derived-scalar for the specified natural twist/scalar comparison, and def-weil-rationalization-karoubi for the actual raw scalar localization and its morphisms. I read each whole statement. The integral comparison is not silently used as a rational theorem: the item's explicit hypothesis supplies it after rationalization. I checked the direction of beta and that conjugating T(f) has exactly B(T(C)) and B(T(C')) as endpoints.

Step 2 uses lem-weil-integral-twist-scalar-coherence. Its statement gives exactly the displayed tower equation, including a on the twisted object and T(a) on the untwisted object, and explicitly identifies its rationalized associator with the canonical scalar composition map. I solved that equality by composing inverses on the two sides; the two rearrangements have compatible source and target.

Step 3 uses def-weil-algebraically-closed-coefficients, whose statement actually specifies both Hom transport by scalar associators and equality after a further common finite extension. It also uses the naturality in lem-weil-integral-twist-derived-scalar, under the rationalized-comparison hypothesis established as notation in Step 1. Substituting Step 2 into a_T(C') B(t(f)) a_T(C)^(-1) gives exactly t(f^G). I checked the cancellations explicitly; it is not an unexplained assertion that the construction transports. No new filtered-colimit theorem is needed because representative equality is in the cited definition itself.

Step 4 again uses that definition for composition at a common finite stage. The two conjugated morphisms have the same intermediate beta, whose inverse cancels. Identity is the same one-line computation. The same hypotheses are stated for -m, so repeating Steps 1–4 for that sign is legitimate.

Step 5 uses lem-weil-integral-twist-base-change, whose statement explicitly includes compatibility of twist-line base change with evaluation, tensor powers and towers. I checked its source sentence in the parent blueprint and read its whole statement for all integers m, including negative dual powers. In this item evaluation compatibility and the inverse evaluation identities are assumed, so I did not attempt to prove finite-stage invertibility from the definition alone. The composite gamma is beta for -m at T_m(C), followed by T_-m(beta for m at C). Thus e_F gamma = B(e_E) is exactly the assumed compatibility, not an extra descent lemma. Rationalization preserves this equality through the explicit Hom-scalar localization definition cited in this step.

Step 6 uses the common-stage definition for classes and their composition. I expanded both twist functors on a representative and checked that the conjugating comparison is precisely gamma from Step 5. Multiplication by the enlarged e on the target side reduces naturality to the assumed finite-stage naturality e_Y T_-T_+(f) = f e_X. This yields an actual natural isomorphism, and its component inverse is already represented at the same finite stage. Both signs are written into the conclusion. This does not use any stronger claim that scalar extensions are fully faithful or that infinite coefficients are a primitive derived ring.

Step 7 uses def-coefficient-twists-detailed, whose statement says that E(m) is the image of the integral twist and Qbar(m) its common-stage extension. The tensor inverse identities on coefficient units are the assumed finite-stage evaluations already used in Steps 5–6. Their compatibility makes their classes the inverse identifications of the two ordered tensor products. I checked both orders, so this is the asserted invertibility of the line, not just a functor with an unspecified inverse.

Hypotheses and small cases: no finite-type, noetherian, finite-dimensional, or structural morphism to a finite field was used for S. All categorical calculations apply to the stages already assumed in the item. The global finite-field notation in the definition node is not turned into a geometric structure on S. For m=0, beta and evaluations reduce to unit comparisons and the formulas give the identity twist. For negative m the same formulas use the assumed dual evaluations. For E=F and F=G they reduce through the canonical unitors to identity transport. Zero objects and zero morphisms cause no exception. Distinct representatives over unrelated finite fields are compared at a further finite compositum, available in the stated directed system. A nontrivial tower associator is retained throughout, so no unjustified strictification is used. All arguments after the supplied comparison maps are explicit compositions and cancellations; no hidden lemma was made a node, no hypothesis was added, and no clause of the item was exported. There is no step exceeding 2,000 characters (lengths: 883, 628, 866, 602, 952, 914, 569). No forbidden SGA source was used.

I corrected no statement or source error. The correction to the imported material is supplying the missing representative-independence, functoriality and inverse-naturality proof. All eleven excerpts in citations.json were checked as literal substrings of the respective cited statements. The first dry run requested a longer excerpt for Step 7; I replaced the short common-stage phrase by the complete defining paragraph, including E(m) as the image of the integral representative and Qbar(m) as its common-stage extension.

## What remains unfinished

Nothing in this item's split. Its existing unsplit input nodes remain separate stage-1 tasks, as permitted for a one-level split. Delivery validation and push follow this report.
