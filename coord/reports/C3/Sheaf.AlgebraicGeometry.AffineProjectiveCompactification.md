## What changed

Proved `AlgebraicGeometry.exists_affine_projective_compactification` in
`Sheaf.AlgebraicGeometry.AffineProjectiveCompactification`, preserving its signature.
A finite generating set gives the closed affine embedding. Adding a `none` coordinate
identifies its affine space with a standard chart of finite projective space.
Mathlib supplies the dense open factorization through the scheme-theoretic image.
The image inclusion witnesses H-projectivity, and the existing dense-open dimension
theorem gives the dimension equality.

Added proof-only imports of `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`
and `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
Updated the item's proof steps and proof dependencies to this implementation.
No definitions, statements, public imports, or consumer modules changed.
The construction permits an empty generator set and the empty source scheme.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_affine_projective_compactification`
(node `lem-kun-compactification-affine`).
No holes added or split off; no `sorry` remains in the delivered module.

Validation: `lcompile.py` compiled the final proof without warnings in 26.1 seconds.
`#print axioms AlgebraicGeometry.exists_affine_projective_compactification` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`; no transitive proof holes remain.
The delivery dry run also checks the module and declaration axioms.

## No longer needed

Removed proof imports:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion`:
  its `exists_isImmersion_projectiveSpace` only retains the projective immersion,
  while this statement also needs the closed affine embedding and distinguished chart.
  The finite affine presentation is constructed directly instead.
- `WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel`:
  its existential proper closed model does not retain the prescribed immersion `j`.
  Mathlib's image factorization applies directly to the constructed immersion.
- `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`:
  the topological density of `j.toImage` is already a Mathlib instance, so no passage
  through scheme-theoretic dominance is required.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` as a direct import:
  the needed quasi-separatedness and quasi-compactness API is publicly provided by
  the affine-space proof import.

Removed proof-dependency edges to `lem-chow-affine-immersion`,
`lem-chow-closed-model`, `lemma-nagata-open-immersion-qc-over-separated-target`,
`def-nagata-scheme-theoretically-dense-open`, and `def-pc-scheme`.
The first two are replaced by their direct construction and the existing
`lemma-nagata-immersion-open-in-scheme-image` Mathlib leaf; the next two supported
a redundant density argument. The scheme definition remains a statement dependency.
No claim is made that these modules or nodes are globally unreachable from other targets.
No top-level `tool_uses` approvals were removed.

## Where the brief, the DAG or earlier work was wrong

The declaration attached to `lem-chow-affine-immersion` proves immersion into projective
space but does not expose the closed affine embedding required by this item. Its source
argument is implemented using existing finite-generation and affine-space declarations.
The declared closed-model theorem similarly chooses an immersion rather than using the
specified `j`. Mathlib's image instances supply exactly the needed construction and
already include topological density, eliminating the DAG's separate sheaf argument.
The unit and chapter routes are preserved, with the same polynomial presentation,
projective closure, and dense-open dimension comparison.

On resumption the original sandbox contained dispatcher metadata only, with no Lean
packet or report to recover. The original `.budget` was preserved unchanged.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
