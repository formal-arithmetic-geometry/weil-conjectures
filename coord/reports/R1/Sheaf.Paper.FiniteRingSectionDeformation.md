## What changed

Reduced `AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coordinate_normalization`
without changing its signature or any definition. The two orientation maps are proved
invertible from `coordinateTowerAdjoint_isIso` and the existing counit-normalized
`SectionLocalDualizingComparisons.sectionLocality` isomorphism. These proofs are private
helpers in the item. A private proved equality identifies the latter locality map with
the item's original `etaleSectionMap`; neither map is redefined.

The remaining calculation is the actual orientation square at the fibre over one,
stated in the new module `Sheaf.Paper.SectionCoordinateTowerOneFibre`. Its inputs
pin the deformation chart to the actual coefficientwise extended-Rees map, followed
by the fixed standard-coordinate isomorphisms. Its statement expands the existing
coordinate and locality formulas with local lets; it introduces no new data definition.
It has no normalized family isomorphism parameter and asserts only the one-fibre
square, with no invertibility conclusions.

The item forms the raw family comparison as inverse family orientation followed by
pullback of the source orientation. Naturality of the section compositor and the
one-fibre square prove this raw comparison is normalized. The existing proved
`existsUnique_normalized` identifies it with the supplied kappa, and inverse
cancellation proves the full family equation. Thus the global normalization and
uniqueness argument is complete Lean, separate from the remaining fibre calculation.

Both new imports of the item are proof-only. Existing public imports, definitions,
instances, signatures and docstrings are preserved. Only the assigned item, its
proof-route node, the new theorem module and its node are delivered.

## Proved and sorry left

The item initially had one hole:
`AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coordinate_normalization`
(node `lem-trf-finite-ring-section-deformation`). Its proof is now complete from the
named inputs, and the item contains zero direct holes.

One hole is added:
`AlgebraicGeometry.Etale.coordinateTowerSection_oneFibre`
(node `lem-trf-section-coordinate-tower-one-fibre`). This is only the one-fibre
compatibility of the two specified orientations, before introducing any normalized
comparison over the whole affine line. Its docstring and node give the source and
complete argument in words.

This is a decomposition: one upper hole closed syntactically, one lower hole added,
net zero holes closed. The two invertibility assertions and the normalization,
uniqueness and inverse-cancellation assembly are proved. No arbitrary witness is
chosen and no definition acquires a hole.

Validation: the final item compiles through `lcompile.py` in 52.0 seconds,
without development profiling options. The new theorem module compiled in
58.6 seconds in the preceding all-files check. Both are below the 60-second
per-file limit. Large local fibre-identification and family-invertibility proof
terms use proved auxiliary lemmas to avoid repeated kernel conversion; no
shared definition or transparency setting was changed.

## No longer needed

The direct proof dependency `lem-trf-section-coordinate-counit-normalization` is
replaced by the narrower one-fibre calculation and the already proved
`lem-trf-coordinate-tower-adjoint-isomorphism`. Its affine-local `Chart` interface is
not instantiated by this proof, whose coordinate map is over a general Noetherian
base. Other users retain that module and node; neither is withdrawn.

No existing import is removed and no module is pruned. All other proof dependencies
remain needed by the unchanged proofs. No unit-level statement or route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The stated coordinate-counit normalization theorem uses a `Chart`, which includes
affineness of its base and coordinate neighbourhood. The assigned theorem assumes
neither. Specializing that theorem directly would add hypotheses. The new statement
isolates the one-fibre calculation with the actual global coordinate map and explicit
geometric typing instances; these instances are all supplied in the item by its
existing `Geometry` and `coordinateDeformationMap_spec`.

The rework table lists an earlier quarantine of the item through an imported false-tail
module. A current item source is present and was copied unchanged before proof edits;
no archive or absent path is withdrawn. The compiler's private dependency overlay
resolves unpublished prerequisites through the normal compilation service. This packet
changes the actual remaining proof rather than merely rebasing the restored module.

Searches were run with `msearch.py` using LeanFinder, Loogle and grep. LeanFinder
returned eight ordinary affine-coordinate/spectrum identities; Loogle and Mathlib
grep returned no specialized match. Local searches found the existing coordinate
adjunction, affine-chart normalization and exceptional-fibre coherence interfaces.
The cited landed declarations are reused; no landed theorem is copied or restated
under another name.

## New nodes

`lem-trf-section-coordinate-tower-one-fibre`, realized by
`Sheaf.Paper.SectionCoordinateTowerOneFibre`, is the actual ordered-counit orientation
square at the fibre over one, in the general coordinate-map case. The source is
`sk-thm-dnc`, Local construction, and orientation-charts Step 3. It is strictly the
fibre calculation: invertibility and the full affine-line comparison are proved in
the parent. Dimension zero, empty schemes and the zero coefficient ring need no
extra assumptions. There is no change record because no existing interface changes.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
