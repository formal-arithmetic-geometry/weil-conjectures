## What changed

Proved `AlgebraicGeometry.ProEtale.SpFiniteOrientation.unit_tower_mem` in
`Sheaf.Paper.FiniteOrientationReduction` with its statement unchanged. Exact evaluation,
the realization counit, and the single-functor comparison identify every finite level
with the regular coefficient module in degree zero. Existing intrinsic coefficient
realization comparisons transfer constructibility and the cohomological and Tor bounds
`[0,0]`. The proof then supplies those same bounds at every level.

Added proved private helpers for these identifications, finite-unit bounds, and
isomorphism transport, together with five private proof imports. Updated step 1,
proof dependencies, and proof origin of `lem-sp-finite-orientation-reduction` to record
the actual argument. No public signature, definition, or consumer changed.

## Proved and sorry left

Closed 1 of the item's 3 initial holes:
`AlgebraicGeometry.ProEtale.SpFiniteOrientation.unit_tower_mem`
(node `lem-sp-finite-orientation-reduction`). Added 0 holes and split off 0 statements.

The two remaining holes, both unchanged and attached to
`lem-sp-finite-orientation-reduction`, are:

- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.uniformizer_orientation_agreement`.
- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.finite_orientation_reduction`.

The finite-unit bounds and finite-evaluation identification were checked separately
with the prescribed compile helper before integrating the tower membership proof.
The integrated module passed the server single-file compile without warnings (57.4 s).

## No longer needed

None. No original imports or dependency nodes were removed. The remaining orientation
holes still require their recorded inputs; this delivery proves the independent
coefficient-unit membership clause.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repairs were needed. In particular membership requires no
normalization of tower reductions, no flatness of coefficient quotient maps, and no
nonempty-scheme or nonzero-ring hypothesis. The proof works uniformly at the first
positive level and for ramified coefficient extensions.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
