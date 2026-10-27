## What changed

Replaced the proof hole of
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_twistedSplitting_components`
by an explicit assembly of the finite splitting, the unit component and the
Chern component. The existing statement and docstring are unchanged.

The categorical argument proves five private helpers in the item module:
`derived_inverse_triangle`, `retwist_shift`,
`retwist_inverse`, `projection_mate_unit`, and `adjoint_shift`.
The inverse-twist calculation uses the exact-localization cocycle and the
ordinary tensor/Hom equivalence triangle. The mate calculation uses naturality
and the adjunction triangle; the shifted mate uses the canonical derived
adjunction shift theorem. Biprod.inl_desc and biprod.inr_desc identify the
components of the actual Model.bq.

Added proof imports of the exact-derived cocycle/coherence modules, the canonical
right-derived adjunction shift theorem, and the two new comparison modules.
All original public imports, definitions and signatures are preserved.
Updated the item's node to describe this argument.

Validation: both new modules compile through lcompile.py, and the final item
compiles without warnings (24.9 seconds). No direct-importer adaptation is
needed because every existing interface is unchanged.

## Proved and sorry left

Original holes: 1. The body of
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_twistedSplitting_components`
is filled completely from the two new named statements and the existing API.
This is a decomposition, not a sorry-free proof of the geometric assertion.
All five private helpers have complete proofs and no holes.

Two holes are added, each as the entire proof of a public theorem:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.positivePullback_unit_square`
  (`lem-sfb-positive-pullback-unit-square`, module
  `Sheaf.Paper.TowerClassPositiveUnitSquare`). This is only the normalized
  coefficient-unit square for positive pullback. It has no projective model,
  splitting, twist cancellation or trace conclusion.
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finite_splitting`
  (`lem-sfb-diagonal-trace-finite-splitting`, module
  `Sheaf.Paper.DiagonalTraceFiniteSplitting`). This is only invertibility at a
  single positive finite level, without either component identity.

Thus one original hole is closed by decomposition and two lower holes remain;
net textual hole change is +1. No hole is placed in a definition.

## No longer needed

No original import is removed. The parent's direct proof dependency
`lem-weil-pbc-ringed-projection-mate-exact`
(`Sheaf.Paper.ProjectionMateExact`) is unnecessary: the required mate and shift
identities are proved explicitly from adjunction naturality, the triangle
identities, and `canonicalRightDerivedAdjunctionShift`.

The parent no longer directly invokes `sk-lem-geo-p1-cohomology`,
`lem-pur-coefficient-system-derived-comparison`, or
`det-sp-coefficient-towers-abelian`. They remain dependencies of the new finite
comparison lemma, so this delivery does not claim to prune their modules.
No unit statement or unit proof step is bypassed; the unit/Chern decomposition
and twisting route of paragraph (1) are retained. No source-library declaration
or module is removed.

## Where the brief, the DAG or earlier work was wrong

The listed dependency signatures do not directly give either the normalized
unit square for PositivePullback or the identification of the actual Model.bq
with the ordinary finite decomposition. GeoP1Cohomology is about ordinary finite
constant coefficients, whereas Model.bq lives in the derived category of strict
varying-ring systems. Its evaluation requires the coefficient, root, adjunction,
line and model comparisons. The two new statements isolate these actual
comparison steps instead of moving the full obligation to another name.

The second component requires coherence of the specific localized tensor/Hom
unit and counit, not just the abstract existence of some equivalence. The proof
uses the ordinary triangle and the exact-derived cocycle to verify that
coherence. Equality is never inferred from finite evaluation on arbitrary
derived arrows.

Edge cases checked mathematically: n=0 corresponds to exponent 1, l=2 uses the
same shift cancellation, empty schemes and charts give zero section identities,
and the unit square makes no invertibility assertion about l on the base.
No definition or statement repair is made.

## New nodes

`lem-sfb-positive-pullback-unit-square` records the coefficient-unit naturality
square for the actual positive-twist comparison. Its source is paragraph (1) of
the current diagonal-tower trace proof and the section normalization of the
same tensor-line projection construction. The docstring gives the pure-tensor
calculation and its exact localization. LeanSearch, LeanFinder, local library
search and blueprint search found no existing specialization.

`lem-sfb-diagonal-trace-finite-splitting` records only the evaluated invertibility
part of paragraph (1). Its proof uses the existing finite Kummer normalization,
derived evaluation comparison and (G2), transported along the specified model.
The docstring explains coefficient level n+1 and the Cartier sign. The same
searches found the ordinary finite decomposition but no theorem identifying it
with this strict-system bq.

No change record is required: no existing signature, definition, instance,
attribute or public import is changed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
