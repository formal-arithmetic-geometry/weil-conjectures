## What changed

Proved `AlgebraicGeometry.nagataQCOpenDescent_chart_le` and
`AlgebraicGeometry.nagataQCOpenDescent_limit_chart_le` in
`Sheaf.AlgebraicGeometry.NagataQCOpenDescent`. Each proof rewrites iterated inverse
images using `Scheme.Hom.comp_preimage`, then uses the corresponding existing
projection identity (`baseChangeDiagram_map_fst` or `baseChangeCone_π_app_fst`).
The resulting inclusion is reflexive. These are exactly the arguments already
recorded in the declaration docstrings; the construction and all signatures stay
unchanged. The module compiled through `lcompile.py` in 3.2 seconds.

## Proved and sorry left

Closed 2 of 2 holes:

- `AlgebraicGeometry.nagataQCOpenDescent_chart_le`
  (node `def-nagata-qc-open-descent`).
- `AlgebraicGeometry.nagataQCOpenDescent_limit_chart_le`
  (node `def-nagata-qc-open-descent`).

No sorry remains in the delivered module. No holes were added or split off.
The existing imported upper-bound theorem is still a dependency of the
finite-stage construction; its proof is outside this item.

## No longer needed

None. Both existing public imports are used by the construction or its types:
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` supplies the
base-changed diagram, cone and projection identities, and
`Sheaf.Order.DirectedFiniteUpperBound` supplies the selected common stage and its
upper-bound property. No modules or nodes are pruned. The finite-data lifting
and section-colimit results mentioned in the docstring justify obtaining the
input choices; this delivery does not change that existing interface or route.

## Where the brief, the DAG or earlier work was wrong

No defect found. The two postponed chart inclusions are equalities after the
projection identities, so they need no affine, compactness, directedness or limit
assumptions beyond their existing signatures. The generic proofs cover empty and
full chart opens as well.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
