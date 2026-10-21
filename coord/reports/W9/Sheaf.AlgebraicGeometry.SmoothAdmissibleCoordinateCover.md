## What changed

Proved `AlgebraicGeometry.SmoothOfRelativeDimension.exists_finite_admissible_coordinate_cover`
without changing its signature. The proof privately imports
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` and reuses the proved
`AlgebraicGeometry.Smooth.exists_etale_to_affineSpace`, which supplies charts of the prescribed
dimension. It chooses a finite subcover, reindexes it by `Fin`, composes each chart with the
base-open inclusion on affine spaces, proves the factorization, and supplies the geometric
properties through Mathlib instances. Updated the existing node's proof to match this route.
All public imports and existing declaration signatures are unchanged.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.SmoothOfRelativeDimension.exists_finite_admissible_coordinate_cover`
(node `lem-sp-smooth-admissible-coordinate-cover`). Holes closed: 1; holes added: 0;
remaining holes in delivered modules: 0. No split-off statements.

The final module compiles through lcompile.py. An additional single-file axiom probe reports
exactly `propext`, `Classical.choice`, and `Quot.sound`. The construction covers empty X
(the subcover of the empty point-indexed family is empty), empty Y, and d=0 uniformly.
The characteristic hypothesis is retained although the proof works over every field.

## No longer needed

Removed these private imports, whose required declarations are supplied by the retained
public imports and the proved chart theorem's import:

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.RingTheory.RingHom.StandardSmooth`
- `Mathlib.Topology.Defs.Filter`

Removed from this node's proof dependencies:

- `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`: the adopted source theorem already
  proves the projection identity using isoSpec naturality; the final gluing uses resLE_comp_ι.
- `lem-weil-pbc-qcqs-over-affine`: compactness and local Noetherianity are obtained directly
  from the finite-type structure maps; no separate quasi-separatedness construction is needed.
- `lem-weil-pbc-qcqs-morphism-permanence`: Mathlib's Noetherian-source instance supplies
  quasi-compactness, and the affine-source separation instance supplies quasi-separatedness.

No Lean modules are withdrawn. No unit statement or route is bypassed. The existing approved
standard-smooth tool use remains, because the reused source theorem uses it internally.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The plan did not identify the existing proved fixed-dimension
scheme chart theorem in the adopted source library; using it avoids redoing the ring-map to
scheme-map conversion. The variable-dimension theorem attached to
`sbc-thm-etale-local-normal-form` remains unnecessary. No changes to definitions or consumers.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
