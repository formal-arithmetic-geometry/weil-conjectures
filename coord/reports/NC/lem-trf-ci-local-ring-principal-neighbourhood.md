1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-ci-local-ring-principal-neighbourhood.json` — target statement split into four proof steps; no new nodes; Mathlib searches found no matching complete-intersection theorem.
- `citations.json` — verbatim statement quotes for every cited node and step.

2. Attachments: none.

3. WANTED: none.

4. What was checked and corrected:

The target node, `sec-trace-formula` chapter, and `sk-i-curve-zero` unit were read. I checked the source statement and proof in Algebra Tags 00SD, 00SF, and 00SG. The target statement is unchanged. The four steps follow the source: choose a polynomial presentation and identify the localized quotient; verify that the polynomial localization is a regular local essentially finite-type presentation; transport the regular-sequence kernel using `lem-trf-essentially-finite-type-ci-kernel-invariance`; and apply `lem-weil-pbc-lci-regular-sequence-global-complete-intersection` to obtain the principal element. I opened each cited node and verified that its statement supplies exactly the fact used: finite-type polynomial presentation, localization of a quotient, regularity of polynomial localizations, essential finite type under localization, invariance of regular-sequence kernels for two regular local presentations, and the principal-neighbourhood conclusion. The quotient map from `A` is local because an isomorphism of local rings preserves the unique maximal ideal; the polynomial localization map is local because its target is the quotient by the localized kernel. Empty regular sequences are covered by the cited invariance and globalization statements. The Mathlib leanfinder, loogle, grep, and leansearch searches were run twice with distinct phrasings; hits concerned smoothness/localization or regular-sequence infrastructure and did not state this theorem.

## Review by NC

I compared every hypothesis in the item with the 00SD local complete-intersection definition and 00SG (1) => (3). In step 1, the finite-type hypothesis gives a polynomial quotient and the cited quotient-localization node identifies its localization with `F_Q`; no extra hypothesis is used. In step 2, the cited polynomial-regularity statement applies at the inverse-image prime, and essential finite type follows directly from the localization definition. In step 3, the given presentation `F_Q ≅ A/(a_1,…,a_c)` supplies a surjective local map from the regular local ring `A`, with the stated regular sequence in its maximal ideal; the cited invariance lemma therefore applies to the polynomial localization map. In step 4, all hypotheses of the cited 00SG globalization lemma are now present with `P`, `I`, and `Q`, yielding `h∉Q` and the asserted global complete intersection. I checked the edge cases `c=0` and `n=0`; the cited statements explicitly allow empty sequences and zero-variable polynomial rings. No duplicate or new node was introduced.

5. What could not be finished: nothing.
