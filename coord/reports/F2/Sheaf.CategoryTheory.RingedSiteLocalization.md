## What changed

Proved `CategoryTheory.ringedSiteSectionLocalization_compatible` in
`Sheaf.CategoryTheory.RingedSiteLocalization` by rewriting successive restriction as
composition in `RingCat`, applying `Functor.map_comp` and `op_comp`, and then using
`Over.w`. This implements the existing docstring's argument directly from Mathlib.
The localization telescope construction and all declaration signatures are unchanged.
The server single-file compiler passed without warnings (1.8 seconds).

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.ringedSiteSectionLocalization_compatible`
(node `def-weil-pbc-ringed-site-section-localization`).
Proved 1 of 1 original sorries; 0 holes added, 0 split off, 0 sorries left.

## No longer needed

None. No proof dependency modules were required or added: the argument uses Mathlib's
composition and slice-category laws already available through the existing imports.
The existing public imports supply the module-sheaf, slice, sequential-colimit and
sheafification infrastructure of the localization construction and are retained.
No DAG dependencies or modules are pruned; the node already has no proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The node records a definition with no proof steps; its
module's compatibility theorem already documents the elementary functoriality proof,
which is now formalized without changing the route or creating nodes.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
