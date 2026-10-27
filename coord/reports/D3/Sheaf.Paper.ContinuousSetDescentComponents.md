## What changed

Proved `AlgebraicGeometry.ProEtale.continuousSet_descent_components` in
`Sheaf.Paper.ContinuousSetDescentComponents`, with its signature unchanged.
The proof uses the existing profinite function sheaf, Mathlib fpqc descent and
continuous forgetful functor, the spectral-component theorem, and Mathlib's
connected-component equivalence. For discrete coefficients it constructs the
open fibre through each point, proves this family is a site covering using
Mathlib's Zariski-precoverage inclusion, and proves local injectivity by
point evaluation or the empty covering. The local-bijection localization
criterion and the sheafification counit prove invertibility of the specified
canonical map. Updated the node proof and dependencies to match.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.continuousSet_descent_components`
(node `lem-sfb-continuous-set-descent-components`).
Added 0 holes, split off 0 statements, and left 0 holes in the delivered module.
Existing imported project theorems are not claimed as newly proved.
The complete module compiled through `lcompile.py` before delivery.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.EtaleComparison`,
`Sheaf.RingTheory.IndEtaleStability`,
`Mathlib.AlgebraicGeometry.AffineScheme`, and
`Mathlib.Topology.Separation.Hausdorff`.
The proof does not require nodes `det-pe-morphisms-etale-comparison`,
`lem-weil-pbc-ind-etale-stability`, or `lem-weil-pbc-affine-scheme-qcqs`:
Mathlib already supplies weakly-etale composition, the etale-to-weakly-etale
instance, and the Zariski-precoverage inclusion. Removed these nodes from this
item's proof dependencies and removed the two obsolete tool-use entries.
This is pruning of this item's dependencies; no source-library declaration or
module is withdrawn. Retained every public import.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned comparison packages were stronger
than necessary. Indexing the fibre cover by source points avoids increasing
the universe of the small-site family when the coefficient type is in u+1.
The construction handles empty U with the empty family, and empty D without
choosing an element. The unit's statement and route remain unchanged.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
