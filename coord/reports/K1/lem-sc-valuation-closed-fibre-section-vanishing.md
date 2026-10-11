Files written:

- `lem-sc-valuation-closed-fibre-section-vanishing.json` — repaired item; no Mathlib match.
- `lem-sc-valuation-limit-qcoh-section-descent.json` — repaired statement-only child; no Mathlib match.
- `citations.json` — verbatim citation for step 2.

Attachments: none.

WANTED: none.

What was wrong and repaired: the item was false when A is a field, since no nonzero maximal-ideal element exists. I added the hypothesis that A is not a field and made the nonzero index explicit. The prior proof also used an arbitrary descended module without identifying it with the restriction of L. It now chooses nonzero pi_0 in m and takes F_{pi_0}=L|X_{pi_0}; all pullbacks are the actual restrictions of L. The helper now states section colimit and eventual vanishing only for a specified finitely presented stage module, so the unnecessary module-descent clause is gone.

What could not be finished: no Lean declaration exists for this item; stage 1 does not write Lean.

## Not duplicates

`lem-sc-valuation-limit-qcoh-section-descent` vs `lem-weil-pbc-limit-global-sections-colimit`: the existing node treats only the structure sheaf, while this child treats a specified finitely presented quasi-coherent module.

`lem-sc-valuation-limit-qcoh-section-descent` vs `lem-pc-fp-module-map-descent`: the existing node descends module maps in Noetherian affine approximation data; this child gives global-section continuity for one specified module on an arbitrary qcqs affine-transition system.

`lem-sc-valuation-limit-qcoh-section-descent` vs `lem-pc-fp-complex-descent`: the existing node concerns bounded complexes, while this child concerns a single finitely presented module and its sections.

`lem-sc-valuation-limit-qcoh-section-descent` vs `lem-pc-finite-flat-proper-support-descent`: the existing node descends finite-flat proper-support data, while this child gives the section colimit and eventual-zero conclusion.

`lem-sc-valuation-limit-qcoh-section-descent` vs `lem-pc-fp-relation-descent`: the existing node descends finite relations among maps, while this child concerns global sections of a fixed module.

`lem-sc-valuation-limit-qcoh-section-descent` vs `lem-pc-flat-bounded-complex-descent`: the existing node assumes flat bounded complexes, while this child has no complex or flatness hypothesis.

`lem-sc-valuation-limit-qcoh-section-descent` vs `lem-pc-noetherian-approximation-data`: the existing node packages Noetherian approximation, while this child is the section-continuity assertion used for the valuation quotient system.

`lem-sc-valuation-limit-qcoh-section-descent` vs `lem-pc-fp-module-map-descent-affine`: the existing node is an affine ring-level map-descent lemma, while this child is a scheme-level global-section colimit statement.

## Review by K1

I reread More on Morphisms Tag 0EX8 and Limits 01Z0, checking every repaired hypothesis. Step 1 uses only the scheme-morphism and invertible-module definition nodes; its valuation divisibility and base-change construction is elementary, with A not a field supplying nonzero pi_0. Step 2 uses exactly the helper sentence quoted in `citations.json`: the section colimit for F_{pi_0} and eventual zero after pullback. Thus it applies directly to s|X_{pi_0}, with no arbitrary model. I searched the DAG and blueprint for duplicates; the existing colimit node is structure-sheaf-only. Mathlib searches in both node files found no exact result. The field case is now excluded, while a DVR supplies nonzero pi_0 and nonempty later stages.

## Second reading by K1

- Item statement: checked against More on Morphisms, Tag 0EX8, including the valuation-ring and closed-fibre setup; verdict: correct with the explicit non-field hypothesis.
- Node `lem-sc-valuation-limit-qcoh-section-descent`: checked against Limits, Lemmas 01ZR and 01Z0; verdict: correct, and generalized to an arbitrary quasi-coherent stage module as 01Z0 states.
- Step 1: checked the cited scheme finite-presentation and invertible-module definitions and the affine base-change construction; verdict: elementary and sufficient, with a nonzero element supplied by `A` not being a field.
- Step 2: checked the cited section-colimit and eventual-zero statement of the helper; verdict: applies directly to the restriction of `L` and `s`, with no unproved finite-presentation claim.
- New-node form: statements are self-contained, use definition nodes for every notion, have Stacks tags and labels, and record the Mathlib searches; verdict: passes B1-B7 and duplicate search.

Changes made: removed the unnecessary finite-presentation requirement from the helper node (and its implied proof obligation), matching Tag 01Z0; retained the explicit non-field hypothesis and the direct restriction construction from the first reading.

