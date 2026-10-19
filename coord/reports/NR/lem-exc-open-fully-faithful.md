1. Files written

- `dag/nodes/sec-smooth-purity/lem-exc-open-fully-faithful.json`: statement node split into four proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every node cited by every proof step.

2. Attachments

- `AlgebraicGeometry.Etale.fullyFaithfulLowerStarOfIsOpenImmersion` belongs to `lem-sc-open-immersion-pushforward-fully-faithful` (the declaration is underived and therefore does not attach this derived item).
- No sorry-free declaration in `WeilConjectures/` states the full derived item.

3. WANTED

- WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/lem-exc-open-fully-faithful.md`, node/order 1809, because that imported source file is not present in this checkout. The split follows the imported proof paragraph while correcting its invalid derived-functor argument.

4. What was wrong in the imported node

The imported paragraph says that exactness of extension by zero implies that its right adjoint (g^*) preserves K-injectives. This uses the wrong functor and does not prove (Lg^*Rg_*). The corrected proof uses exactness of inverse image (g^{-1}), preservation of K-injectives by its right adjoint (g_*), and K-injective computation of (Rg_*). The imported paragraph also omits the existing underived open-immersion counit lemma and the existing disjoint open/closed vanishing lemma; both are cited explicitly in the repaired split. The displayed second identity is read in the usual termwise derived sense, with (i_*) applied to complexes and (Lg^*) represented termwise because (g^{-1}) is exact.

5. What could not be finished

No Lean declaration proving the complete derived statement was found, and no new Lean or compiler work is permitted at stage 1. The natural-language split and its citation audit are complete.

## Review by NR

I read the imported item, the `sk-prop-sf-existence` unit and chapter records, and the relevant source files in `/home/ubuntu/weil-src-slopmaster2`: `SixFunctors/Etale/LowerShriek/OpenImmersion/FullyFaithful.lean` for the underived open-immersion counit, `SixFunctors/Etale/Derived/UpperLowerStar.lean` for the derived upper/lower-star construction, and `SixFunctors/OpenClosed/Derived.lean` for the disjoint-support derived vanishing pattern. I also opened every DAG node cited by the four steps, including the exactness and termwise-derived-factorization nodes, K-injective resolution/total-derived/Hom nodes, the right-adjoint K-injective lemma, the underived open-immersion full-faithfulness node, and `lemma-openclosed-vanishing-lowerstar`; each citation quote in `citations.json` is copied verbatim from its node statement.

Step 1 verifies the adjunction direction (g^{-1}\dashv g_*), the open-immersion counit isomorphism, exactness of inverse image, and the termwise realization of its derived functor. Step 2 verifies existence of K-injective resolutions, computation of the total right derived direct image on a K-injective, preservation of K-injectives by (g_*) because (g^{-1}) is exact, and the Hom/naturality comparison. Step 3 applies the natural counit termwise to the K-injective representative and checks that localization gives (Lg^*Rg_*\cong\mathrm{id}), with resolution independence supplied by the K-injective comparison statements. Step 4 checks that the hypotheses of the disjoint open/closed vanishing lemma match (g) and (i), then applies exactness and termwise derived factorization degree by degree to obtain (Lg^*i_*=0). I corrected the imported extension-by-zero/reversed-adjunction inference and added the missing inverse/direct-image and immersion definitions to `stmt_deps`.

## Second reading by NR

- Step 1: checked the inverse/direct-image adjunction and counit against `def-weil-pbc-inverse-image` and `lem-sc-open-immersion-pushforward-fully-faithful`, exactness against `prop-weil-pbc-inverse-image-exact`, and termwise derived factorization against `lem-weil-pbc-exact-functor-derived-factorization`; every cited statement supplies the asserted input, and the step is not elementary.
- Step 2: checked the K-injective existence, total-derived computation, right-adjoint preservation, and Hom comparison against the four cited statements, with the adjunction orientation matched as (g_*\dashv g^{-1}); all hypotheses are present and the step is not elementary.
- Step 3: checked the termwise counit complex, localization, and resolution-independence against the underived counit, total-derived, K-injective Hom, and exact-factorization statements; the naturality and derived identity follow from those statements, and the step is not elementary.
- Step 4: checked disjointness and sheaf-level vanishing against `lemma-openclosed-vanishing-lowerstar`, exactness and termwise derived realization against the two inverse-image nodes, and the meaning of termwise (i_*) against `def-weil-pbc-direct-image`; the degreewise zero-complex argument is explicit and the step is not elementary.
- New nodes: there are no new nodes in this split; the item's existing dependency nodes were checked for self-contained statements, definition citations, source places, and recorded Mathlib searches. The whole-blueprint search and the imported blueprint source were checked; no duplicate or Mathlib leaf replaces the item.
- Edge cases checked: the zero complex and empty open/closed pieces make both displayed identities zero or identity as stated; a field and a one-point open immersion reduce to the ordinary adjunction counit; no hypothesis is lost when the complement is empty.

Changes made: clarified that (i) is the scheme-theoretic closed complement and that the displayed (i_*) is applied termwise on complexes, added the direct-image definition to step 4's dependencies, and added its verbatim citation. This closes the implicit underived/termwise transition while preserving the source statement and the corrected K-injective proof.
