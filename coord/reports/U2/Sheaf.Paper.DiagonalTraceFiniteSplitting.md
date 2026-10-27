## What changed

Kept the signature and public imports of `Sheaf.Paper.DiagonalTraceFiniteSplitting` unchanged.
Replaced its hole by a cohomology proof of the actual evaluated biproduct-desc map.
Exact evaluation preserves the concentration of the coefficient unit in degree zero and
of the inverse line shifted by minus two in degree two. Two proved private additive-category
lemmas show that the surviving component suffices in each degree.

Added proof imports of `DiagonalTraceFiniteUnitCohomology`,
`DiagonalTraceFiniteChernCohomology`, and the existing exact-derived-functor API.
The two new modules isolate the unit outside degree two and the Chern component in degree
two, respectively. Both retain the ordinary derived projective-line decomposition (G2)
as their geometric input; they do not assume the system splitting or a trace.
No existing definition, instance, public signature, or other module was changed.

Validation: both new statement modules compiled through lcompile.py; the corrected
item then compiled without warnings in its single-file check (13.4 seconds).

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finite_splitting`
(node `lem-sfb-diagonal-trace-finite-splitting`) by a complete assembly proof.
The item module has zero remaining holes.

Added two holes, each the entire body of one public theorem in its own module:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finite_unit_cohomology`,
  node `lem-sfb-diagonal-trace-finite-unit-cohomology`.
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finite_chern_cohomology`,
  node `lem-sfb-diagonal-trace-finite-chern-cohomology`.

This is a decomposition: one old hole closed, two new holes added; it is not a proof
of the geometric input without new assumptions. Each new theorem concerns only one
component and omits the other component's conclusion. The unit theorem has no Chern or
twist data. The Chern theorem asserts only the map on degree-two cohomology.
The two private biproduct lemmas are proved with no holes.

## No longer needed

No original Lean import was removed, and no module or node is claimed globally pruned.
The parent assembly no longer directly invokes
`lem-pur-coefficient-system-derived-comparison`, `def-sp-tower-class-finite`, or
`sk-lem-geo-p1-cohomology`: the geometric comparisons and G2 now belong to the two
component obligations. Finite Chern normalization and G2 remain necessary there.
The specialized proved `lem-sp-tower-geometry-adjunction-evaluation` supplies the
normalization used in their proof plans, rather than a new generic comparison assumption.
The parent still uses exact evaluation, the model's degree-zero constructions, and
cohomological detection of derived isomorphisms.
No unit-level step is bypassed and no upstream declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan suppresses the identification of the
actual evaluated unit and untwisted Chern component with the ordinary finite G2 maps.
Those identifications are not supplied by G2 alone: it is formulated for fixed-scalar
module sheaves, whereas the tower evaluation takes values in intrinsic ring-sheaf
modules, and the Chern component uses the specified finite normalization and untwisting.
The new docstrings retain those comparisons explicitly instead of assuming a
projective-line splitting for the system.

Edge cases checked: degree two uses only the Chern component; every other integer degree
uses only the unit component. The concentration argument covers negative degrees and
all degrees greater than two. The finite exponent n+1 is positive even at n=0.
Neither component argument requires nonzero coefficients. The model is transported by
its equality over S, and the Chern theorem retains p.finiteX when applied.

The blueprint-ancestor helper returns no ancestor for the existing item because its
creation record names a module. The new nodes preserve the existing node's explicit
blueprint ancestry, prepending this node to the recorded via list.

## New nodes

`lem-sfb-diagonal-trace-finite-unit-cohomology`, in
`lean/Sheaf/Paper/DiagonalTraceFiniteUnitCohomology.lean`, isolates the finite
coefficient-unit computation on cohomology outside degree two. Its proof follows the
unit component of derived G2 after normalized evaluation and exact realization.

`lem-sfb-diagonal-trace-finite-chern-cohomology`, in
`lean/Sheaf/Paper/DiagonalTraceFiniteChernCohomology.lean`, isolates the actual second
component in degree two. Its proof follows finite Kummer normalization, untwisting,
and the Chern component of derived G2. It makes no assertion in other degrees.

Both nodes record LeanSearch, LeanFinder, and source searches. Existing G2 is retained;
no matching system-component theorem was found. No change record is needed because
there is no shared definition or statement repair.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
