## What changed

Proved `AlgebraicGeometry.exists_admissibleBlowup_cartierBoundary_of_coe_support_eq_compl_with_density`
in `Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier`, preserving its signature.
The admissible center is explicitly `I`; principalization gives its invertible transform.
The support-comap identity identifies its complement with the inverse image of `U`,
so `IsInvertible.compl_support_dense` supplies density. For every further blow-up,
`IsInvertible.comap_blowupMap` supplies invertibility; the same support identity and
Cartier-complement theorem supply the remaining clauses.

The node's admissibility step now follows the actual disjoint-support fields of
`IsAdmissible`. Its other three proof steps and the unit's route are retained.
All public imports and all definitions are unchanged. The proof records
quasi-compactness of `U.ι` from `hU`, as in the original admissibility step.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_admissibleBlowup_cartierBoundary_of_coe_support_eq_compl_with_density`
(node `det-nagata-boundary-divisor-cartier`). Added zero holes and split off zero statements.
The item has zero remaining holes. The proof uses the existing declared theorem
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.compl_support_dense`
(node `lem-pc-cartier-divisor-nowhere-dense`), whose own existing hole is unchanged.
This is a proof from the declared dependencies, not a claim that their entire
transitive axiom closure has been closed.

## No longer needed

Removed the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic`.
Removed `lemma-nagata-ideal-unit-off-support` from this node's proof dependencies:
the admissibility structure requires support disjointness directly, which follows
by rewriting the given support equality. No upstream declaration or module is
withdrawn; the Basic module may remain transitively imported elsewhere.
Every other declared dependency is retained. No new modules or nodes are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The original admissibility step performed an
unnecessary affine unit-ideal calculation for the Lean structure's actual interface.
The proof handles empty schemes and the opens bottom and top without selecting
points or assuming the original open is dense. Further centers need only be blow-up
centers for Cartier total-transform persistence; their admissibility is available
but no stronger condition is required by that theorem.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
