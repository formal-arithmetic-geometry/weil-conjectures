## What changed

Proved `AlgebraicGeometry.vanishing_linear_system_isImmersion` with its original signature.
The proof writes the ideal-coordinate products as linear combinations of the given sections,
constructs a projective morphism from normalized linear forms on each target basic open,
identifies its composite with the fixed very ample embedding by coordinate ratios, and uses
immersion cancellation and locality near the image.

Added `Sheaf.DeligneLaumon.BertiniProductCoordinates`, proving
`AlgebraicGeometry.bertini_product_coordinate_relations`. Its products are explicit: multiply
an ideal-twist generator by a pulled-back projective coordinate and transport through the
tensor-power isomorphism. The theorem proves vanishing on the closed subscheme, coverage by
generating loci on its complement, and the coordinate-ratio equations. It has no field,
finite-coordinate, span, or immersion hypothesis or conclusion.

Used the existing proved `generatingSections_pair` and native projective chart interfaces.
The private tensor, ideal-image and pullback calculations preserve canonical adjunction
units; no shared definition, existing public import, or existing statement changed. Updated
the item's DAG proof and added the product-coordinate node. Empty schemes, empty coordinate
families and `n = r` require no exclusions: the covering and tensor-power arguments apply
uniformly.

Both modules compiled through `lcompile.py --all`; the fresh compiles took 20.2 s for
the product calculation and 19.7 s for the item. The original theorem signature was checked
byte for byte. Its unused-result-binder lint is disabled locally to preserve the existing
`hspan` and `hvalue` names; these hypotheses are used in the proof.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.vanishing_linear_system_isImmersion`
(`lem-zl-bertini-product-system-immersion`).

Also proved the new theorem
`AlgebraicGeometry.bertini_product_coordinate_relations`
(`lem-zl-bertini-product-coordinate-relations`) and all private helpers.
There are zero `sorry`s left in either delivered module and zero holes added or split off.
Existing imported declarations are used as the library states them.

## No longer needed

Removed these original private imports from the item:

- `Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage`: its packaged statement uses
  `ULift (Fin (n+1))`; `generatingSections_pair` and native chart APIs work directly with the
  arbitrary finite index type in this item.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`: the native `homOfSections` API
  constructs the normalized chart map directly.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`: the native standard-open cover,
  projective-pair frame/relation APIs and chart-ratio extensionality suffice.
- `WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`: the existing
  `exists_generatesAt_of_epi` applies directly to the possibly infinite ideal generating
  family, and the needed tensor nonvanishing equivalence is proved in local frames.
- `WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections`: moved to the proved
  product-coordinate module; its kernel statement is still needed.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`: no direct use in the
  item; it remains a transitive dependency of `NonvanishingTensorPullback`.

The first four modules are absent from this delivery's import closure, so their packaged
nodes (`lem-weil-pbc-projective-morphism-chart-preimage`,
`lem-weil-pbc-projective-space-functor-of-points`,
`lem-weil-pbc-projective-space-standard-charts`,
`lem-weil-pbc-invertible-generating-sections-fibre`) are no longer dependencies of this route.
They can still be needed by other routes. No source-library declaration or module is
withdrawn. The tensor-pullback node is still needed transitively and is not claimed pruned.
The kernel, immersion composition, cancellation and locality nodes remain needed.

The new product module imports `SectionAvoidance` directly and proves the short monoidal
restriction calculation privately; it does not import `HilbertPolynomial` for that one
calculation. Redundant exploratory imports of `VeryAmple` and `FieldBaseChange` were removed
from that new module, and `NonvanishingGeneratingLocus` was removed from the item after the
comparison proof was replaced by `generatingSections_pair`.

## Where the brief, the DAG or earlier work was wrong

The item statement is unchanged and no mathematical error was found. Several planned
packaged projective lemmas are unnecessarily restricted to the standard nonempty coordinate
index type. The proved native APIs provide the chart argument for arbitrary coordinate
types, including empty types. The product identities and all gluing are proved here; no
renaming or repackaging of the original immersion obligation is left as a hole.

## New nodes

`lem-zl-bertini-product-coordinate-relations`, in
`dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-product-coordinate-relations.json`,
records the proved explicit product calculation. Its source is Stacks Project, Varieties,
Tag 0FD5, the proof of `lemma-generate-over-complement` and its displayed product fractions.
It realizes the product calculation below the existing unit's immersive-system route.
No change record is needed: no existing interface or definition changed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
