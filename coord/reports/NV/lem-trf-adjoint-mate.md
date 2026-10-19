# Stage-1 report: lem-trf-adjoint-mate

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-adjoint-mate.json`: item converted to a Mathlib leaf; no new nodes.
- `citations.json`: empty, because the Mathlib leaf has no split proof steps.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, blueprint tag, and adjunction/mate names. No sorry-free project declaration states this item exactly. The declaration with the blueprint tag in the shared working Lean tree is outside the mandated attachment source checkout and was not treated as an attachment.

## WANTED

None.

## What was checked and corrected

The imported item had a three-paragraph Hom-bijection/Yoneda proof with no dependencies and status `imported`. The complete statement is already the general categorical mate construction in Mathlib, so I removed that proof sketch, set `status` to `mathlib`, and recorded the exact Mathlib declarations used. The triangulated-category, shift, and exactness assumptions are unused specialization context and do not alter the categorical conclusion.

I searched the whole DAG and blueprint for the item and for conjugation/mate statements. The closest existing records are `lem-sf-mate` (a composition-specific specialization) and `lem-weil-pbc-conjugate-iso-unit-equation` (the opposite direction, an isomorphism of right adjoints determining a left adjoint map); neither states this complete left-adjoint-isomorphism item, so neither is cited or duplicated.

## Not duplicates

No new nodes were created. The two closest existing records were inspected and differ in direction or in their composition-specific hypotheses, as described above.

## Review by NV

I read the item node, its chapter and unit records, the imported blueprint proof text, and the relevant Mathlib source. In `Mathlib/CategoryTheory/Adjunction/Mates.lean`, `conjugateIsoEquiv` (line 425) constructs an equivalence from isomorphisms of left adjoints to isomorphisms of right adjoints. Its generated `conjugateIsoEquiv_apply_hom` and `conjugateIsoEquiv_apply_inv` formulas specialize exactly to the displayed composites for beta and beta inverse. The component formulas `unit_conjugateEquiv` (line 300) and `conjugateEquiv_counit` (line 285), with the inverse variants, give every unit and counit identity in clause (2), including the exchanged versions. Since `conjugateEquiv` is an equivalence, its injectivity gives the uniqueness clause. I also read the source around `conjugateEquiv_iso` to verify that the induced transformation is invertible. I checked the hypotheses: Mathlib only requires categories, functors, adjunctions, and the natural isomorphism, so the item's stronger triangulated/exact context is a valid specialization. Small edge cases such as identity functors and identity alpha reduce to the identity conjugation by the Mathlib `conjugateEquiv_id` law. The Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as such in the node. No correction to the mathematical statement was needed.

## Second reading by NV

- Item statement: checked every category, functor, adjunction, unit, counit, isomorphism, and all three numbered clauses against the blueprint node and its proof; the triangulated/exact hypotheses are harmless specialization context, and identity adjunctions pass the edge-case check.
- Step 1: checked against the blueprint Hom-bijection paragraph and `def-weil-pbc-adjunction-conjugate`; its specialization with $\\tau=\\alpha^{-1}$ gives the displayed component and inverse formulas and invertibility.
- Step 2: checked the unit calculation against the triangle identities and naturality of $\\alpha$; the exchanged calculation is written explicitly rather than asserted by “similarly”.
- Step 3: checked the counit calculation against the mate formula, naturality of $\\alpha$, and the inverse mate; both original and exchanged counit equations are stated.
- Step 4: checked uniqueness objectwise using naturality of $\\beta'$ and the $(F_1,G_1)$ triangle identity; this proves equality from the unit condition, so the additional counit condition is redundant.
- Existing dependency `def-weil-pbc-adjunction-conjugate`: read its complete statement and Mathlib source match; it is the existing generic conjugation fact, not a new duplicate. No new nodes were created.

I changed the item from an overbroad Mathlib leaf to a four-step split. The previous leaf recorded only `conjugateIsoEquiv` and did not provide the item’s explicit unit/counit derivations or the uniqueness argument. The repaired split cites the existing generic conjugation node, spells out the remaining calculations, and keeps `citations.json` verbatim for both non-elementary uses.
