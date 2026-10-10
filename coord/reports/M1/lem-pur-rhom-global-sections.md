Files written: item `dag/nodes/sec-smooth-purity/lem-pur-rhom-global-sections.json`; no new nodes; 1 Mathlib leaf used (`lem-weil-pbc-kinjective-hom-derived`).

Attachments: none.

WANTED: `literature/stacks-project/sites-cohomology.tex`, Lemma 08JA and its proof (including 0A94 and the K-flat-to-K-injective lemma), for `lem-pur-rhom-global-sections`.

The item was not already stated by a sorry-free declaration in `WeilConjectures/`. I checked the surrounding purity nodes and the source checkout for the blueprint tag and relevant RHom/global-sections declarations. The statement was retained. The imported node had only one grep search, so I replaced it with the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches required for this item. No duplicate child node was created: the needed K-injective localization input already exists as the Mathlib leaf `lem-weil-pbc-kinjective-hom-derived`.

## Review by M1

I read the item, `def-pur-derived-internal-hom`, `lem-pur-rhom-well-defined`, `prop-pur-kinjective-resolutions-exist`, and the existing K-injective localization leaf. Step 1 uses the resolution-existence statement for the K-injective target, the derived-Hom definition for the representative, and the well-definedness statement for independence; each cited statement supplies exactly that input. Step 2 uses the derived-Hom representative and the leaf's bijection from homotopy-class maps into a K-injective complex to derived-category maps; degreewise evaluation of global sections is the definition of Gamma in the item. Step 3 uses quasi-isomorphism invariance and the leaf's homotopy-equivalence consequence to obtain canonical independence and naturality. The small test cases are a one-point ringed site (where Gamma is the identity and the claim reduces to the usual Hom-complex computation) and L=M=0 (both sides are the zero group). The source text is missing locally, so the proof is marked agent-origin and the requested source is listed above.

## Second reading by M1

- Item statement: checked against the recorded Stacks tag 08JA statement and its cited definitions; the small ringed site, derived category, K-injective representative, and canonical H^0 identification are all stated.
- Step 1: checked against `prop-pur-kinjective-resolutions-exist`, `def-pur-derived-internal-hom`, and `lem-pur-rhom-well-defined`; removed the unsupported K-flat assertion and used only the cited representative-independence result.
- Step 2: checked against `def-pur-derived-internal-hom`, `def-pur-hom-complex`, and `lem-weil-pbc-kinjective-hom-derived`; wrote the degreewise global-sections calculation and the K-injective localization bijection for H^0.
- Step 3: checked against `lem-pur-rhom-well-defined` and `lem-weil-pbc-kinjective-hom-derived`; expanded the representative-change and naturality argument so the elementary label is justified.
- New nodes: none; the existing Mathlib leaf `lem-weil-pbc-kinjective-hom-derived` was checked for its exact declaration and recorded search results.
- Small cases: the one-point ringed site reduces to the usual Hom-complex computation; L=M=0 gives zero on both sides; the empty site has zero global sections and zero Hom group.

Changes made: removed the unsupported K-flat hypothesis and its unsupported use, and made the final naturality argument explicit. The Stacks source file named by 08JA is absent from this checkout, so the proof remains marked as an agent reconstruction.
