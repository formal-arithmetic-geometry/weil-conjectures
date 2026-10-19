## What changed

Proved `AlgebraicGeometry.reducedBoundary_smoothOfRelativeDimension_zero` in
`Sheaf.AlgebraicGeometry.Curve.ReducedBoundarySmooth`, preserving its complete signature and
public imports. The proof bounds the dimension of the curve by mapping each finite chain into
an irreducible component. The dense open makes its closed complement nowhere dense, and the
existing dimension-drop theorem bounds the boundary dimension by zero. Mathlib then makes the
boundary finite, discrete and affine. Its global sections form a finite reduced algebra over
the perfect base field, so the existing proved source theorem
`Algebra.Etale.of_isReduced_of_perfectField` gives etaleness and Mathlib gives smoothness of
relative dimension zero. The empty case uses the empty supremum defining scheme dimension.

Added only private proof imports for the algebra, Artinian and affine criteria. Updated the
item node's proof, proof dependencies, proof origin and obsolete tool approvals to describe
this shorter route. Recorded the already-proved algebra theorem as an existing source leaf;
there is no new Lean module or declaration. The blueprint unit statement and steps remain.

Validation: the final module compiles without warnings through `lcompile.py` in 4.8 seconds.
Edge cases checked: empty boundary (the section algebra is zero), an empty curve, disconnected
pure-dimensional curves, and finite residue extensions that are not rational over the base.
No choice of data from an unproved existence theorem is used.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.reducedBoundary_smoothOfRelativeDimension_zero`
(node `lem-a1-reduced-boundary-smooth`).

Added 0 holes and split off 0 statements. No `sorry` remains in the delivered Lean module.
The proof uses the existing `AlgebraicGeometry.dim_le_zero_of_isNowhereDense`, whose own
proof remains an existing dependency item. The new source-leaf node attaches to the already
proved `Algebra.Etale.of_isReduced_of_perfectField`; it introduces no hole.

## No longer needed

Removed the original private proof imports:

- `Mathlib.AlgebraicGeometry.ResidueField`.
- `Mathlib.RingTheory.KrullDimension.Zero`.
- `Sheaf.AlgebraicGeometry.ClosedPointField`.
- `Sheaf.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields`.
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`.

The affine finite reduced algebra theorem replaces the singleton residue-field construction,
residue-field finiteness argument, coproduct gluing and coproduct etaleness theorem. Mathlib's
etale instances supply exactly the smoothness conclusions, so the stronger fibre-dimension
comparison theorem is unnecessary. No public import was removed. The residue-field and zero-dimensional-ring imports were
also present in the current repository version; this proof obtains the needed algebra
criteria from the retained Artinian modules and the added source theorem.

Removed proof dependencies:

- `def-weil-affine-spectrum`.
- `lem-weil-pbc-minimal-prime-reduced-localization-field`.
- `def-weil-residue-field`.
- `lem-kun-closed-point-field`.
- `lem-weil-pbc-scheme-coproduct-family`.
- `lem-exc-etale-coproduct-etale`.
- `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.

Retained the original dimension-drop and comparison dependencies, Artinian finite-discrete
result, and finite-discrete affineness result. Pruned the obsolete top-level tool approvals
for `lem-kun-closed-point-field`, `lem-weil-pbc-scheme-coproduct-family`,
`lem-exc-etale-coproduct-etale` and `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.
These dependencies are unnecessary for this proof; other parents may still use them.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's singleton-decomposition route is mathematically valid
but longer than applying the already-proved finite reduced algebra criterion to the whole
affine boundary. The existing docstring explains that valid original route; the updated DAG
records the shorter Lean implementation. Initial compile-server requests twice returned no
answer while the server was busy; a subsequent request compiled normally.

## New nodes

`lem-a1-finite-reduced-perfect-algebra-etale` records the existing proved source theorem
`Algebra.Etale.of_isReduced_of_perfectField` from
`WeilConjectures.Mathlib.RingTheory.Etale.Field`. A finite-dimensional reduced algebra is a
finite product of finite field extensions, which are separable over a perfect field; Stacks
Algebra Tags 00JB and 00U3 give the argument. Its complete existing Lean proof was read.
LeanSearch, LeanFinder/Loogle and local Mathlib/library/DAG searches are recorded in the node.
It has `lean.existing: true` and requires no new module, theorem, change record or consumer
adaptation. It is a strictly algebraic supporting result, not a restatement of the boundary
geometry theorem.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
