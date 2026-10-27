## What changed

Proved `WeilConjectures.PurityFiniteSetting.chartCartesianDomain` with its signature and
`ChartCartesianDomainConclusion` unchanged. Constructed the prescribed open complement directly,
lifted the diagonal by the universal property of open immersions, and proved both required
Cartesian squares. Two proved private helpers implement the open cut and graph pullback.
Finiteness, separatedness, smoothness, and etaleness use the existing permanence APIs.
Added the private proof import
`WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` for the
base-change squares of the two factors. Updated the existing node's proof route.

## Proved and sorry left

Closed the original one hole: `WeilConjectures.PurityFiniteSetting.chartCartesianDomain`
(node `lem-pur-chart-cartesian-domain`). Added zero holes and split off zero statements.
No `sorry` remains in the delivered module. The final remote compiler run passed cleanly
in 14.4 seconds. `#print axioms` reported exactly `propext`, `Classical.choice`, and
`Quot.sound`; the temporary print command was removed before delivery. The private helpers `cartesianOpenCut` and
`mapGraphPullback` are completely proved.

## No longer needed

Removed these private proof imports:

- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.

Removed the following unused nodes from this item's proof dependencies:

- `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`: only relative dimension zero is needed;
  Mathlib's existing etale instance supplies it, without the separate fibre-dimension theorem.
- `def-weil-unramified-morphism`: Mathlib's etale diagonal instance directly supplies the
  open immersion; the library's conjunction definition is unused.
- `lem-weil-pbc-locally-noetherian-quasi-separated` and
  `lem-weil-pbc-qcqs-morphism-permanence`: the Noetherian-source quasi-compactness instance
  handles the open inclusions and e directly.
- `lemma-nagata-finite-type-to-separated-target`: e is locally of finite type by etaleness,
  and quasi-compact because its source is Noetherian.

These are removals from this item's route only; no library file or declaration is withdrawn.
All public imports and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement repair was necessary. The original plan used stronger auxiliary finiteness
and fibre-dimension results than this conclusion needs. Empty opens and d = 0 require no
special branch; all constructions and universal properties work uniformly. Y is never
assumed separated over the field: absolute separatedness is used only after restriction
to the affine open V.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
