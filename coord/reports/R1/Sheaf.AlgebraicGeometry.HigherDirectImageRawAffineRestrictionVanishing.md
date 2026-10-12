## What changed

Proved `AlgebraicGeometry.Etale.exists_higherDirectImage_raw_affine_restriction_eq_zero`
from affine raw cohomology comparison injectivity. Added the module
`Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective` for that
strictly smaller geometric obligation. The original theorem signature and docstring are
preserved. A private proved helper establishes filtered additive colimit zero detection.
Restriction naturality is obtained from the canonical natural transformations
supplied by the new comparison interface, whose components are fixed by equations
to equal the explicit raw pullbacks. The latter uses Mathlib `IsColimit.eq_iff'`, with explicit universe
shrinking for preservation of filtered colimits by the forgetful functor.

The proof first restricts the class to W, uses the comparison cocone and its injective
colimit map, finds a stage killing that class, and uses naturality to obtain uniform
vanishing on every further restriction. No arbitrary witness is used to define data:
existential comparison data are eliminated only in a theorem proving a proposition.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_higherDirectImage_raw_affine_restriction_eq_zero`
(node `lem-sbc-higher-direct-image-raw-affine-restriction-vanishing`).
There is no sorry left in the assigned module. The private helper `exists_addCommGrp_stage_eq_zero` is proved.
The raw transition and limit maps are natural transformations with prescribed
components; their naturality is part of the geometric comparison obligation.

Added one hole:
`AlgebraicGeometry.Etale.exists_raw_affine_colimit_comparison_injective`
(node `lem-sbc-raw-affine-colimit-comparison-injective`). This is a decomposition, with
one hole closed and one added, not a complete proof of geometric continuity. The new
statement supplies a cohomology diagram with canonical maps and an injective comparison;
it asserts neither eventual zero nor uniform vanishing under restrictions.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`
  (node `lem-weil-pbc-etale-cohomology-limit-complex-systems`).
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
  (node `sbc-lem-higher-direct-image-presheaf`).

These modules remain needed below the geometric comparison or through the retained
public definition import; no claim is made that they leave the whole target closure.
The original natural-comparison module and upper-star coherence public imports remain.
Added proof imports of the new comparison module and Mathlib filtered-colimit APIs.

Discarded the saved attempt's holed stage-zero theorem/node, because Mathlib proves
that step directly. Also discarded its unused transition-complex presentation and
complex-class-vanishing route; neither module is added or imported by this delivery.
The unit's cohomology-continuity route is preserved by the new geometric comparison.

## Where the brief, the DAG or earlier work was wrong

The saved attempt had not compiled within the 60-second limit and left an elementary
filtered-colimit criterion as an additional sorry with an incomplete new-node record.
That criterion is now proved privately, and the extra node is not delivered.
The original raw comparison interface described only functions on one affine object.
The final interface supplies the raw maps as additive natural transformations on the
whole site, with their components explicitly equated to the raw pullbacks. This is
canonical functorial cohomology comparison, rather than any vanishing conclusion.
The resulting proof uses their naturality squares directly, avoiding repeated
expansion of derived-category constructions. The new comparison's docstring and
node describe the construction and naturality of those transformations, before
applying geometric cohomology continuity. No time limit, existing definition,
existing statement, or trusted axiom is changed. The original stage
plan's base-change, derived-Hom identification, and continuity steps remain explicitly
recorded in the new comparison node and its full natural-language proof.

The comparison statement was checked against
[Stacks 09Z1](https://stacks.math.columbia.edu/tag/09Z1),
[Stacks 03Q8](https://stacks.math.columbia.edu/tag/03Q8), and
[Stacks 0EZM](https://stacks.math.columbia.edu/tag/0EZM).
Degree zero is section continuity; the empty affine object gives zero groups.
No forced adaptations or interface changes to existing declarations are made.
The new module introduces `RawAffineColimitComparisonData`, a type packaging actual
categorical data and their required equations. Its existence theorem asserts
`Nonempty` of that type. The assigned proof eliminates this witness only to prove a
proposition; no definition chooses arbitrary data from an unproved existence theorem.
Bundling the data avoids repeated expansion of large raw-presheaf types in nested
existential elimination. On this retry both modules compiled without warnings in 29.0 and 25.9 seconds,
respectively, using `lcompile.py --all`. The previously reported target-module timeout
did not recur. The delivery dry run supplies the remaining checks.

## New nodes

`lem-sbc-raw-affine-colimit-comparison-injective`, in
`dag/nodes/sec-smooth-base-change/`, records the canonical raw affine cohomology
comparison, its canonical natural transformations with prescribed components, stage/leg
equations, and injectivity. Its module is
`Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective`.
Its proof describes the affine base change, coefficient single-complex construction,
natural derived-Hom identification, and application of complex cohomology continuity.
It has no eventual-zero conclusion and is strictly a part of the original argument.
No change record is needed: all existing signatures and visibility are preserved.

## Second reading by R1

1. I compared the delivered restriction-vanishing module with the repository version. The theorem signature and docstring are unchanged byte for byte; only proof text and proof-only imports were changed. The added comparison module and node are declared in the report and do not alter existing declarations.

2. I compiled both delivered modules with `lcompile.py --all` and compiled the target module individually. They compile without errors or warnings. The only remaining `sorry` is the named theorem `exists_raw_affine_colimit_comparison_injective`; it is the split-off node recorded in the new module and DAG. No forbidden `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition occurs.

3. The split-off comparison statement is a genuine lower-level injectivity and naturality obligation. It does not restate the target's eventual vanishing conclusion, and its structure packages actual categorical data rather than defining data from an unproved witness. Its source, proof plan, searches, and Lean declaration are recorded in `lem-sbc-raw-affine-colimit-comparison-injective.json`.

4. I checked the proof route top-down. The target uses the comparison's natural transformations, the filtered-colimit zero criterion, and their naturality to obtain one later stage working on all restrictions. The previous direct continuity and presheaf proof imports are removed and listed under `## No longer needed`; the smooth-base-change unit route remains represented by the comparison node.

5. The DAG proof, proof dependencies, proof origin, Lean declarations, and `realized` unit route agree with the delivered Lean code. The original target node is closed at the target level, while the lower comparison node remains explicitly split.

I changed only this report section after the worker delivery; no Lean proof or statement was altered during second reading.
