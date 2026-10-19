## What changed

Completed all four theorem proofs in `lean/Sheaf/Paper/FiniteMittagLeffler.lean`.
The finite tower proof uses Mathlib's finite cofiltered-system theorem on finite prefix
solution sets, then the existing Roos cokernel description. The two abstract Milnor
results use `milnor_shortExact`; the completed-adic result compares the supplied triangle
with the canonical triangle from `pbcRoosTriangle`.

## Proved and sorry left

No `sorry` remains in the item module. Proved:
`CategoryTheory.finiteTower_mittagLeffler_vanishing`,
`CategoryTheory.milnorMap_isIso_of_finite`,
`CategoryTheory.milnorMap_single_isIso_of_finite`, and
`AlgebraicGeometry.ProEtale.completedMilnorMap_isIso_of_finite`.
Closed four original holes; added zero holes. No statements were split off.
The existing imported Roos and Milnor results remain dependencies.
The module compiles cleanly through `lcompile.py`.

## No longer needed

Removed proof-only imports of `Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty` and
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`; the proof uses Mathlib's
`nonempty_sections_of_finite_cofiltered_system` and no fully-faithful API. The latter
import was only in the retained sandbox.
Also removed the current source's direct imports of
`WeilConjectures.AlgebraicGeometry.MLSetsTowerLimitNonempty` and
`Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups`: the former is unused, while the
latter remains a used dependency already publicly imported by the Milnor and Roos modules.
The node `lem-weil-pbc-ml-sets-tower-limit-nonempty` and its source module
`WeilConjectures.AlgebraicGeometry.MLSetsTowerLimitNonempty` are not needed by this proof: the
finite special case is already in Mathlib. Removed the corresponding obsolete top-level
`tool_uses` entry `lem-weil-pbc-ml-sets-tower-limit-nonempty` from the node.
All other declared dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

The retained proof needed explicit finite instances and explicit `Fin` bounds in the
prefix construction. The source interfaces were otherwise sufficient; no statement
correction was needed. Updated the proof route and dependencies in
`lem-weil-pbc-mittag-leffler` to record the finite Mathlib special case and triangle comparison.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
