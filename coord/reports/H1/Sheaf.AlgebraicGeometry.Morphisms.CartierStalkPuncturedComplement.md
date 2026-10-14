## What changed

Proved `AlgebraicGeometry.Scheme.cartier_stalk_punctured_complement` with its original signature and visibility. Added the proof-only import `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat` for the proved `Scheme.flat_fromSpecStalk` instance. Added three fully proved private helpers: `fractionRing_away_uniformizer`, `dvr_prime_dichotomy`, and `cartier_preimage_closedPoint`.

The Cartier ideal pulls back to an invertible ideal on the local spectrum. Its chart through the closed point is the whole spectrum, so its nonzero generator excludes the zero prime. The DVR prime dichotomy identifies its support with the closed point. The fraction-field map is localization away from a uniformizer; its open range is exactly the other point. Mathlib's open-immersion lifting and pullback criteria finish the original square.

Updated the existing node's proof, proof dependencies, and proof origin to match this argument. No statement, definition, public import, target, or other module was changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.cartier_stalk_punctured_complement` (node `lem-sbc-cartier-stalk-punctured-complement`): 1 of 1 original sorries proved. No sorries remain in the item; no holes were added or split off. All three private helpers are proved. The delivery axiom probe checks all new declarations against the three permitted axioms.

## No longer needed

Removed proof dependency `def-pc-integral-scheme` from this node: the proof does not use the quotient-field description of the generic stalk of D. The assumptions `hD` and `hη` remain unchanged in the original signature; the proof explicitly acknowledges them to avoid unused-variable warnings. Local Noetherianity is also unnecessary for the local argument, and stays in the signature.

Imports removed: none. Modules pruned: none. All four original public imports support the unchanged signature or its definitions. The Cartier, DVR, and fibre-product dependencies remain. No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The previous proof plan's quotient-stalk identification is unnecessary: a nonzero Cartier ideal on a DVR has the closed point as its support even without identifying that ideal with the maximal ideal. This is a shorter route below the unit level. Edge cases: a unit generator would have empty support, excluded by the specified point in the centre; a zero generator violates the nonzerodivisor hypothesis; a field is excluded by the DVR instance. The chosen generator and uniformizer come from proved theorems, and the final morphism is explicitly constructed with the open-immersion lift.

## Second reading by H1

1. Interface: PASS. Compared the only delivered Lean module and node with the repository using diff. The existing theorem signature is byte-for-byte identical, including every hypothesis, conclusion, and visibility. No existing definition or docstring changed. The only added import is private to the proof. Only the node's `proof`, `proof_deps`, and `proof_origin` differ; there are no change records or other delivered modules.

2. Proof and axioms: PASS. Compiled the module through `lcompile.py` without errors or warnings (5.2 seconds). Compiled a scratch copy with `#print axioms` for `fractionRing_away_uniformizer`, `dvr_prime_dichotomy`, `cartier_preimage_closedPoint`, and `cartier_stalk_punctured_complement`: each uses exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Checked the delivered Lean for forbidden declarations and sorry: none. The chosen Cartier chart and uniformizer come from proved results; the final morphism is constructed by `IsOpenImmersion.lift`, not chosen from an unproved existence theorem.

3. Split-off statements and edge cases: PASS. No statements were split off and no holes were added. Read all three proved private helpers. The localization helper covers every nonzero denominator by a power of the uniformizer; the prime dichotomy follows from the DVR being a local Dedekind domain. For the Cartier support helper, flat pullback preserves the nonzerodivisor generator, an open containing the local closed point is the whole spectrum, and the nonzero generator excludes the zero prime. A unit generator contradicts the assumed centre point, a zero generator contradicts regularity, and a field is excluded by the DVR class. Thus the helper does not silently require a reduced divisor or a generator equal to the uniformizer.

4. Shortest route, imports, and unit: PASS. Searched Mathlib with the fresh Loogle query `IsFractionRing, IsLocalization.Away` (no hits) and a DVR grep for `closedPoint|isMaximal|localization`, and searched both Lean roots for the punctured/Cartier-complement and helper terminology. `SmoothTraitAffineGenericOpen` has a similar private helper, unavailable as a public reusable declaration, with a longer direct localization construction; its public theorem has additional smooth-family data and does not replace this argument. The support and open-immersion APIs already used provide the direct reduction. All four original public imports provide signature vocabulary; the new plain import supplies the proved flat-stalk instance. The sole old proof dependency omitted is `def-pc-integral-scheme`, already listed above. No imports or modules are pruned. Read `dag/units/sk-prop-input-spreading.json`: its realized lists are empty, and its trait-case step is retained; the revised local support argument bypasses no unit. The unchanged theorem docstring describes the original, valid quotient-stalk route rather than the shorter implemented route; the report and node describe the implemented route, and the existing docstring is preserved.

5. DAG correspondence: PASS. Read the item node, all four old proof dependencies and their Lean/Mathlib records. The two new proof steps describe the flat Cartier pullback, DVR spectrum, away-localization, explicit lift, and pullback criterion used in Lean. Their `uses` union is exactly the recorded three-element `proof_deps`. `proof_origin` identifies this argument and its source. Statement, statement dependencies, Lean signature record, chapter, and unit are unchanged. There are no new nodes requiring additional metadata.

Second-reading changes: appended this review and recorded fresh searches only. No Lean or node repair was necessary. Holes closed: `AlgebraicGeometry.Scheme.cartier_stalk_punctured_complement` (1 of 1); holes added: none; split off: none.
