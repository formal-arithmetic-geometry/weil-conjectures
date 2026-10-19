1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-finite-singleton-fibre-stalk-ring.json` — statement split into the finite and finitely presented stalk-map clauses.
- `dag/nodes/sec-trace-formula/lem-trf-localization-finite-ring-map.json` — Mathlib leaf, exact `RingHom.finite_localizationPreserves`.
- `dag/nodes/sec-trace-formula/lem-trf-localization-finite-presentation-ring-map.json` — Mathlib leaf, exact `RingHom.finitePresentation_localizationPreserves`.
- `citations.json` — verbatim statement quotes for every proof-step citation.

2. Attachments: none.

3. WANTED: none.

4. What was wrong in the imported item or route: the item was unsplit. Its existing Mathlib searches described the absence of a direct singleton-fibre theorem, but the proof needs the more general localization-preservation declarations, which were searched and recorded as the two Mathlib leaves. The proof uses the existing `lem-trf-unique-prime-localization` statement rather than its proof, and the affine stalk-localization node to identify the geometric stalk map.

## Review by Q72

I read the item source at Stacks More on Morphisms Tag 05B8, especially the affine proof of assertions (2) and (3), and checked the current unit `sk-i-curve-zero` and chapter `sec-trace-formula`. Step 1 chooses affine neighbourhoods around the two points, uses the finite-morphism definition for an affine finite ring map, and uses the affine-point and affine-stalk-localization nodes for the primes and stalk rings. The singleton-fibre hypothesis supplies exactly the unique-prime hypothesis required by `lem-trf-unique-prime-localization`; its statement gives the localization isomorphism. The new Mathlib leaf `lem-trf-localization-finite-ring-map` says that this localized map remains finite, so the stalk map is finite. Step 2 uses the same affine setup, applies the existing affine finite-presentation criterion for a locally finitely presented morphism, then applies the new Mathlib finite-presentation localization leaf and transports through the same two localization identifications. I verified that every cited node says the fact used, recorded each quote in `citations.json`, and checked edge cases such as an identity finite map (one-point fibre) and a finite local algebra with a unique prime over the base prime. No hypotheses were added or dropped, no definition was changed, and no duplicate blueprint node or Lean attachment exists.
