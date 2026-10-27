## What changed

Replaced the proof of `diagonalTrace_finite_unit_cohomology` by an explicit
cohomological extraction from the existing `geoP1Cohomology` decomposition (G2).
The coefficient ring is the actual quotient supplied by the tower base; the
proof checks its annihilating exponent and invertibility on S. The negative
Tate summand is concentrated in degree two. Exact comparison and realization
preserve its vanishing in the requested degree. The proof constructs the inverse
of the first biproduct injection after homology, composes with (G2), identifies
that component by the biproduct equations, and transports it through the unit
comparison square. The cohomology calculation is a private theorem for an
arbitrary exact coefficient functor; it specializes to intrinsic realization
only once in the public theorem. The square is packaged as an isomorphism in
`Arrow`, and a generic private helper transports invertibility across it.

The new module `Sheaf.Paper.DiagonalTraceUnitArrowComparison` isolates the
remaining arrow comparison. Its statement is a commuting square between the
actual evaluated tower unit and the ordinary finite coefficient unit followed
by the canonical direct-image mate, with source and target isomorphisms. Its
proof docstring spells out evaluation, scalar normalization, constant-object
realization, the bounded-below direct-image comparison, and transport along the
projective-line model. The item's existing signature and public import are
unchanged. Only private proof imports were added to it.
Local reducibility controls and scoped instance exclusions avoid expensive
elaboration without changing exported attributes. Profiling options were removed.

## Proved and sorry left

Original holes: 1. Replaced hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finite_unit_cohomology`
(node `lem-sfb-diagonal-trace-finite-unit-cohomology`). No holes remain in the
item module.

Added holes: 1:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_unit_arrow_comparison`
(node `lem-sfb-diagonal-trace-unit-arrow-comparison`).

This is a decomposition, with net hole count zero, rather than a complete
sorry-free proof. The new obligation is the normalization step of the original
plan: it has no degree q, no cohomology assertion, no invertibility assumption
on l on S, and no use of invertibility of (G2). The independent geometric and
cohomological step is fully written in Lean in the item module. Negative degrees
and the zero coefficient ring use the same vanishing/biproduct argument.

Validation: both sandbox modules compile through `lcompile.py`; the final
item-only compile completed cleanly in 6.4 seconds against the compiled
comparison module. The original signature and the new node/Lean signature were
compared verbatim, and all Lean lines satisfy the 100-character limit.

## No longer needed

No existing module is withdrawn and no existing public import is removed.
Removed a redundant direct import of `SfIntrinsicRealizationTransport` from the
new comparison module: its statement uses the realization equivalence already
publicly available through `TowerClassDiagonal`. Its normalization theorem is
still a proof dependency of the new node.
The unit's route through `sk-lem-geo-p1-cohomology` is retained and used directly.
The original normalization dependencies
`lem-sp-tower-geometry-adjunction-evaluation`,
`def-sp-tower-class-diagonal`, and
`def-sp-finite-intrinsic-direct-adjunction` are carried by the new normalization
node; they remain needed and are not claimed as pruned.
No Chern comparison, trace construction, or tower splitting theorem is imported
as a new proof dependency.

## Where the brief, the DAG or earlier work was wrong

The original plan's first step combines several comparisons for which the
listed declarations supply the ingredients but no composite unit-arrow
identity. `geometry_adjunction_evaluation` compares the system and intrinsic
finite adjunctions; it does not identify the coefficient object with the
fixed-scalar etale constant object. The intrinsic realization comparison fixes
the ordinary and derived direct-image maps, while the projective-line
coordinate records require, rather than construct, their unit comparisons.
The new node exposes precisely this remaining step. The extraction from (G2)
needs only additive biproduct identities and exact-functor homology comparison.
No statement or definition correction was made.

## New nodes

`lem-sfb-diagonal-trace-unit-arrow-comparison` is the comparison of the two
coefficient-unit arrows before the cohomology argument of paragraph (1) of
`sk-prop-diagonal-tower-trace.proof.md`. Its sole remaining hole is in
`Sheaf.Paper.DiagonalTraceUnitArrowComparison`. It has the original node's
chapter and unit and cites the existing evaluation and realization interfaces.
The item node now records the actual cohomology extraction and the use of this
square. The normalization node uses
`lem-sfb-unbounded-direct-image-bounded-below` as the general comparison tool on
the constant object, and the already proved
`lemma-nagata-projective-space-base-change-proper` to check its geometric
hypotheses. No change record is needed: no existing interface was changed.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
