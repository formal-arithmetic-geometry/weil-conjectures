# Stage 1 report

1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-double-complex-homotopy.json` — item, split.
- `dag/nodes/sec-abelian-varieties/lem-sp-ce-horizontal-lift.json` — statement-only child, no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sp-ce-vertical-nullhomotopy.json` — statement-only child, no Mathlib match.
- `citations.json` — verbatim step citations.

2. Attachments: none. No sorry-free project declaration states this item.

3. WANTED: none.

4. The item was unsplit. I retained its statement and split the proof at the two substantive stages: horizontal comparison lifting and vertical null-homotopy of the residual defect. The final two steps assemble the total homotopy and check the filtration shift. The two child statements are strict intermediate interfaces and are not restatements of the total conclusion.

## Review by K1

I reread the imported item and `thm-sp-grothendieck` final paragraph, the existing comparison-homotopy node, and the source route corresponding to Stacks Tags 015I and 015K / Weibel 5.7.10. The first return identified three interface gaps, and I repaired each one. The horizontal child now states the full typed augmentation and exact/injective row hypotheses and explicitly says every `s_1^{p,bullet}` is a map of column complexes. The vertical child now introduces both augmentations, exact augmented source rows with `0 -> Z_I^p -> I^{p,bullet} -> B_I^{p+1} -> 0`, injective target rows, and the hypothesis that `R` vanishes on the augmentation; it states the comparison-theorem row null-homotopies and their assembly into an `s_2` commuting with horizontal differentials.

Step 1 uses the horizontal child for the typed `s_1`, its augmentation identity, its column-complex identity, and the residual `R` vanishing on the augmented row. Step 2 uses the vertical child for the row comparison null-homotopies, exact-sequence assembly, vertical identity, and horizontal compatibility; it no longer asserts that induced row maps are literally zero. Step 3 expands the total differential into all three bidegree components and cites both child statements for the identities that discharge those components, while `def-sp-double-complex-total` supplies the sign convention. Step 4 uses `def-sp-filtration` and first-quadrant boundedness for the filtration shift. Each citation quote in `citations.json` is copied verbatim from the cited statement.

I checked hypotheses at each interface: augmentations and the prescribed `w=d_Ls+sd_K` identity are present in the horizontal child; exact source boundary/cycle/cohomology rows, the displayed short exact sequence, and injective target rows are present in the vertical child; first-quadrant vanishing is present throughout. Small tests on the zero double complex and a one-column complex concentrated in vertical degree zero remain consistent. Mathlib searches for both children used LeanFinder, Loogle, source grep, and LeanSearch; generic homotopy infrastructure appeared but no Cartan--Eilenberg theorem, with the unavailable LeanSearch responses recorded as unavailable. Blueprint and DAG searches found no duplicate statement.

The repaired split therefore addresses return points 1 (typed augmentation hypotheses and corrected vanishing condition), 2 (comparison-theorem null-homotopies assembled through the exact sequences), and 3 (column-complex property and all three total-differential components).

## Not duplicates

`lem-sp-ce-horizontal-lift` vs `lem-sp-cartan-eilenberg-comparison-homotopy`: the child constructs only the horizontal component and residual vertical map, while the existing node compares complete total maps only in a different functoriality setting.
`lem-sp-ce-vertical-nullhomotopy` vs `lem-sp-cartan-eilenberg-comparison-homotopy`: the child kills a residual vertical defect under zero row-map hypotheses; it does not assert existence of either total homotopy component or the total identity.
`lem-sp-ce-horizontal-lift` vs `lem-sp-cartan-eilenberg-double-complex-homotopy`: horizontal component only, versus the full total homotopy.
`lem-sp-ce-horizontal-lift` vs `lem-sp-cartan-eilenberg-properties`: comparison lift, versus structural CE resolution properties.
`lem-sp-ce-horizontal-lift` vs `lem-sp-cart-eilenberg-left-exact-cohomology`: row comparison, versus preservation of horizontal cohomology by a left exact functor.
`lem-sp-ce-horizontal-lift` vs `lem-sp-cartan-eilenberg-exists`: homotopy component, versus existence of a CE resolution.
`lem-sp-ce-horizontal-lift` vs `lem-weil-pbc-cartesian-eilenberg-functorial`: homotopy lift, versus functorial comparison-map construction.
`lem-sp-ce-horizontal-lift` vs `lem-weil-pbc-horseshoe-morphism-lift-exact-source`: double-complex row component, versus a single horseshoe middle-map lift.
`lem-sp-ce-vertical-nullhomotopy` vs `lem-sp-cartan-eilenberg-double-complex-homotopy`: residual vertical null-homotopy only, versus the full total identity.
`lem-sp-ce-vertical-nullhomotopy` vs `lem-sp-cartan-eilenberg-properties`: defect killing, versus structural CE properties.
`lem-sp-ce-vertical-nullhomotopy` vs `lem-sp-cart-eilenberg-left-exact-cohomology`: vertical homotopy, versus left exact cohomology comparison.
`lem-sp-ce-vertical-nullhomotopy` vs `lem-sp-cartan-eilenberg-exists`: null-homotopy, versus resolution existence.
`lem-sp-ce-vertical-nullhomotopy` vs `lem-weil-pbc-cartesian-eilenberg-functorial`: residual correction, versus functorial lift.
`lem-sp-ce-vertical-nullhomotopy` vs `lem-weil-pbc-horseshoe-morphism-lift-exact-source`: vertical defect, versus horseshoe middle lift.

What could not be finished:

- Nothing in the stage-1 split; the child proofs are intentionally downstream unsplit statements.

## Second reading by K1

- Item statement: checked against the imported Stacks tag index entries for Tags 015I and 015K and the existing Cartan--Eilenberg definitions; verdict: hypotheses and conclusion are retained and the zero and one-column cases are consistent.
- Step 1: checked against `lem-sp-ce-horizontal-lift`; verdict: the cited interface supplies the typed horizontal component, augmentation identity, and vertical residual map.
- Step 2: checked against `lem-sp-ce-vertical-nullhomotopy`; verdict: the cited interface supplies the vertical homotopy and horizontal compatibility under the stated zero row maps.
- Step 3: checked against `def-sp-double-complex-total`; verdict: the sign expansion is elementary from the total differential convention.
- Step 4: checked against `def-sp-filtration`; verdict: the degree and first-quadrant filtration check is elementary.
- `lem-sp-ce-horizontal-lift`: checked for B1--B7, source Tag 015I, duplicate search, and zero/one-column cases; verdict: repaired to introduce $K,L$, both augmentations, the differentials, and the typed homotopy data explicitly.
- `lem-sp-ce-vertical-nullhomotopy`: checked for B1--B7, source Tag 015I, duplicate search, and zero/one-column cases; verdict: repaired to introduce the abelian category, both double complexes, the typed residual morphism, and TeX notation explicitly.

Changes made: replaced undefined prose (`I to J`, “complex map on the augmentations”, and untyped `s1`/`s2`) in both child statements with self-contained typed TeX statements; no proof step or citation was changed.

## Source error

The imported source labels are correct: Tag 015I is `derived-lemma-cartan-eilenberg` and Tag 015K is `derived-remark-functorial-ss`. Their text proves existence of Cartan--Eilenberg resolutions and states functoriality of the associated spectral sequences, but it does not state the explicit filtered total homotopy asserted here. The split therefore records 015I/015K for the hypotheses and functorial context and supplies the omitted horizontal/vertical comparison-homotopy argument explicitly, with Weibel, *Homological Algebra*, Lemma 5.7.10 as the mathematical source for that argument. This is a source omission, not a change to the target statement.
