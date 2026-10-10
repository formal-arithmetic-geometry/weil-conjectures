# Stage 1 report

1. Files written: item node plus four statement-only nodes: `lem-pc-rf-base-change-complex`, `lem-pc-noetherian-approximation-data`, `lem-pc-noetherian-perfect-direct-image`, and `lem-pc-perfect-pullback-locality` (all no Mathlib match).
2. Attachments: none.
3. WANTED: `literature/stacks-project/perfect.tex`, Lemma 36.30.1 / Tag 0A1H, for `lem-pc-proper-support-perfect-direct-image` (the repository has only the citation index).
4. The item is the general tensor-and-proper-support theorem used as the classical input in the parent node. Its Lean audit is `none`; searches of both source checkouts found no exact declaration. The returned review identified four non-elementary inputs that had been omitted, so they are now separate statement-only nodes rather than hidden in proof prose. Mathlib searches found only generic declarations, not these Stacks results.

## Review by J1

The second reading verified the item against Tag 0A1H and checked each step against the exact statement of every cited node. The new nodes cover the 0A1G bounded-complex base-change hypotheses, all 01ZR/0C0C/support/09RK approximation hypotheses, the 0A1F Noetherian conclusion, and pullback plus Zariski locality of perfectness. Every citation quote is copied verbatim, and the finite-presentation, flatness, proper-support, and perfectness hypotheses were checked in the relevant steps.

## Not duplicates

lem-pc-rf-base-change-complex vs def-pc-derived-direct-image: the existing node is only the definition of the derived direct-image functor, while the new node is the Tag 0A1G theorem asserting a canonical base-change isomorphism for bounded complexes termwise flat over the base.

I read the item node, its parent `lem-pc-rf-perfect-base-change`, the unit record, and the blueprint ancestor reference. For step 1 I checked the exact hypotheses and conclusion of the new 0A1G node: bounded termwise S-flat complex under a quasi-compact quasi-separated morphism, giving the canonical derived base-change isomorphism. For step 2 I checked the existing 01ZM statement and the new combined node, which explicitly supplies finite-presentation, flatness, proper-support, and perfect-object descent with the cited tags 01ZR, 0C0C, the proper-support limit lemma, and 09RK. For step 3 I checked that the new 0A1F node states the required Noetherian perfect direct image and that the pullback/locality node states both perfectness properties used to descend and glue. `citations.json` now quotes each cited statement verbatim. Small cases (identity morphism, empty support, and a degree-zero flat module) remain consistent. The source absence is recorded as `WANTED`.

5. What remains: the proof depends on the unavailable local Stacks source as a classical input; no Lean implementation is attempted at stage 1.

## Second reading by J1

- Item statement: checked against Stacks Lemma 36.30.1, Tag 0A1H, hypothesis by hypothesis (finite-presentation morphism, perfect E, bounded finitely presented S-flat complex, proper support, perfect direct image, arbitrary base change); verdict agrees.
- Step 1: checked against the Tag 0A1H proof's invocation of Lemma 36.26.4 (Tag 0A1D); verdict repaired to use the exact arbitrary-E/base-change statement and marked non-elementary.
- Step 2: checked against the Tag 0A1H Noetherian approximation paragraph (Tags 01ZM, 01ZR, 0C0C, the proper-support limit lemma, and 09RK); the combined descent node states every non-elementary fact used.
- Step 3: checked against the Tag 0A1H invocation of Lemma 36.27.2 (Tag 0DJQ) and the final pullback/gluing; the Noetherian theorem is cited by its current tag, while pullback preservation and Zariski locality are written directly from the local definition.
- New nodes: three statement-only nodes remain; the pullback/locality node was removed because its source was vague and its claim is elementary from the perfect-complex definition.
- Small cases: identity morphism, empty support, degree-zero flat module, and n = 0/1 reduce to the tensor unit, zero complex, and ordinary proper pushforward cases; no statement change was needed.
- Mathlib searches: the recorded leanfinder, loogle, grep, and unavailable leansearch searches for all four nodes were checked; no direct declarations match these Stacks results.

Changes made: corrected the base-change citation from section tag 0A1G to Lemma 36.26.4 Tag 0A1D and restored its perfect factor and precise comparison map; corrected the Noetherian theorem to Tag 0DJQ and the approximation tags to 05LY, 081G, and 09RF; removed the vague pullback/locality node and gave its short local argument in step 3. The local source file is absent; current Stacks pages were checked for these tag identities.
