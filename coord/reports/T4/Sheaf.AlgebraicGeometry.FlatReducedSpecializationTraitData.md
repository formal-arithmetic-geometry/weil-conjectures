## What changed

Proved `AlgebraicGeometry.exists_flat_reduced_specialization_trait_data` in its
original statement. The trait comes from the adopted source theorem; both sections
are explicit pullback lifts. Mathlib instances establish preservation of the four
morphism properties, Noetherianity of the trait, total space and closed fibre, and
topological Noetherianity. The existing arbitrary-field algebraic-closure criterion
and the cartesian square of ordinary fibres give both reducedness conclusions.
The existing section-component cartesian theorem gives the locus equality and the
last connected-component assertion. Updated the item's DAG proof to this route.

Validation: the delivered module compiles cleanly through `lcompile.py` in 4.4 s,
with no warnings. Its original theorem signature and every public import are
unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_flat_reduced_specialization_trait_data`
(node `lem-trf-flat-reduced-specialization-trait-data`).
No holes added, no split-off statements, and no `sorry` left in the delivered module.

## No longer needed

Removed the proof import of
`Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange` and the proof dependency
`lem-trf-geometric-reduced-fibre-locus-base-change`. Instead, transport geometric
reducedness directly in the cartesian square of ordinary fibres. This avoids its
still-unproved theorem and the auxiliary comparison of arbitrary choices of
algebraic closures.

The node no longer needs `lem-weil-pbc-lft-pointwise-criterion`: the existing
Mathlib instance converts local finite presentation to local finite type directly.
It also no longer needs `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`:
`IsNoetherian.noetherianSpace` gives the requested topology directly, without
reconstructing it through minimal elements of closed-subset families.

Removed the redundant proof import of
`Mathlib.AlgebraicGeometry.Geometrically.Integral`; the algebraic-closure test
already publicly imports it. All public imports are preserved. No module is withdrawn; the unit route is
preserved. No dependency's global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan needlessly passed through the
unproved universal reduced-fibre-locus theorem although only one geometric fibre
was needed. Mathlib already supplies the fibre square, the geometric-reducedness
base-change API, local finite presentation implying local finite type, and
Noetherian schemes' topological Noetherianity.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
