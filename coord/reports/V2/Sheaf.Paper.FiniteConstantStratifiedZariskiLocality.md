## What changed

Proved `AlgebraicGeometry.ProEtale.finiteConstantStratified_zariski_locality` with its
statement unchanged. Private helpers transport finite constant models and stratifications
across isomorphisms, pull stratifications back along arbitrary scheme morphisms, and glue
from affine neighbourhoods using the existing geometric stratification-gluing theorem.
The finite-open-cover clause uses affine opens subordinate to the covering members; the
reverse affine-local implication uses the same gluing helper directly. The pullback
geometry is exposed through an existential theorem before transporting modules, and
finite-cover geometry is kept abstract while transporting its models; this prevents
repeated kernel unfolding of chosen schemes and cover reindexings. Updated the DAG
proof to match this argument. No new public declarations or definition changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.finiteConstantStratified_zariski_locality`
(node `lem-sfb-constructible-zariski-locality`). No holes added or split off. Every private
helper is proved. No `sorry` remains in the delivered module. The complete file
compiled in 4.3 seconds even with a reduced diagnostic heartbeat budget; final
validation removes the diagnostic options and checks the ordinary settings.

## No longer needed

Removed public imports `Sheaf.Topology.ProfiniteCondensedRing`,
`Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`, and
`Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`, and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: their additional interfaces
are not used by the statement or proof. The defining constructibility module already
provides the coefficient, stratification and topological quasi-separatedness types
used by the unchanged statement. No scheme quasi-separatedness criterion is used.
There are no current Lean importers of this item.

The proof no longer needs `lem-weil-pbc-quasi-separated-affine-cover-criterion`,
`lem-weil-pbc-constructible-open-restriction`, `lem-weil-pbc-affine-scheme-qcqs`,
`det-def-sfb-constructible-local-model`, or `def-constructible-stratification` as separate
proof dependencies. `Scheme.Stratification.pullback` supplies the full constructible
stratification, the existing model predicate supplies the witnesses, and arbitrary
pullback stability avoids the auxiliary qcqs checks on covering members. Removed the
three corresponding obsolete approved top-level tool uses, retaining the other four
in their original order. The unit route and geometric gluing core remain in use.
These nodes remain available in the DAG; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier plan is mathematically valid but asks for redundant checks: the current
`Scheme.Stratification.pullback` already preserves constructibility for arbitrary maps.
The gluing core now accepts `Scheme.Stratification` directly, despite its older node
attachment mentioning `LocallyClosedStratification`. The proof uses its current,
stronger interface with explicit constructibility fields. Empty schemes and empty
covers are handled by the finite-subcover construction without any nonemptiness
assumption. No statement or definition repair was needed.

Change record: `coord/changes/V2-finite-constant-locality-imports.md`.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
