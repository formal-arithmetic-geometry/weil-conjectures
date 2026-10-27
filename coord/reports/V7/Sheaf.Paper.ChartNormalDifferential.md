## What changed

Proved `AlgebraicGeometry.ChartNormalDifferential.comparison` by constructing the specified
open neighbourhood, its Cartesian square, the two canonical graded maps, and their actual
relative-spectrum maps. The section formulas retain the second-minus-first convention.
The differential is the conjugate of the normalized normal map; its `IsDifferential` field
is checked on every local `da`. The proof includes dimension zero and empty sources.

The existing public definitions, structure fields and theorem signature are preserved.
Private proved helpers provide the geometric, adjunction and section calculations. The DAG
proof record follows this route; no source-library declaration is changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.ChartNormalDifferential.comparison`
(node `lem-pur-chart-normal-differential`), the module's one original hole.
Holes closed: 1. Holes added: 0. Remaining in this module: 0. No holes are split off.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`:
  the canonical conormal interface is already available through graded base change.
- `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`:
  the existing anti-equivalence is already available through the normal-bundle construction.
- `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`:
  the Cartesian assertion follows from affine pushforward base change and reflection of
  isomorphisms by the anti-equivalence.
- `WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineSections` and
  `WeilConjectures.AlgebraicGeometry.DiagonalConormalDifferentials`:
  the normalized derivation and affine comparison prove the required isomorphism directly.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`:
  its universal-property declaration is already available through the tangent construction.

The proof no longer calls `lem-pur-chart-cartesian-domain`: the required special case is
proved directly using the etale diagonal and the open-immersion pullback criterion.
It also no longer calls `lem-weil-pbc-relative-spec-base-change`,
`lem-sc-diagonal-conormal-affine-sections`, or
`lem-sc-smooth-proper-diagonal-conormal-differentials`; these obsolete direct proof
requirements and their top-level tool approvals are removed from the node copy.
Other dependencies still used through public definitions or canonical interfaces are retained.
No module is withdrawn, and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The regular-diagonal declaration only supplies positive codimension. The theorem here includes
`d = 0`, which is handled separately using the etale diagonal's stalk isomorphisms, the empty
regular sequence and invariance of Krull dimension under ring isomorphism.

The source and conormal constructions use two different ideal models: the closed-immersion
ideal sheaf and the categorical kernel of the structure-sheaf map. The proof supplies their
canonical isomorphism and transports the normalized derivation across it. No statement repair
is required.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
