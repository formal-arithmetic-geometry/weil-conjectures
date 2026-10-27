## What changed

Proved `AlgebraicGeometry.ProjectiveSpace.p1_diagonal_ideal_on_chart` with its
statement unchanged. Added private proof imports of
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination` and
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical`, and private proved
helpers in the item module. No other existing Lean module was changed.

The proof tests the determinant on arbitrary scheme morphisms into the product
chart. Its vanishing is equivalent to agreement of the two projections: the
normalized coordinate families become proportional by a unit, then chart ratio
extensionality applies. Testing on the actual quotient by the determinant ideal
gives the reverse ideal inclusion. This works over arbitrary bases and includes
nonreduced and zero rings. Updated the item's DAG proof to match this route.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProjectiveSpace.p1_diagonal_ideal_on_chart`
(node `lem-sp-p1-diagonal-local-ideal`).

Added 0 holes and split off 0 statements. There are no remaining `sorry`
declarations in the delivery. All private helpers have complete proofs.

Validation: the complete item module compiles cleanly through `lcompile.py` in
8.0 seconds, with no warnings. The unchanged public theorem signature and
100-character line limit were also checked. The delivery tool performs the
required axiom probe and preflight before pushing.

## No longer needed

No pre-existing imports were removed and no entire module is withdrawn.
The original proof dependencies concerning standard coordinates and kernel
ideals remain relevant. The existing chart-ratio extensionality node and the
proved projective-space properness node are also used. The planned four explicit product-chart ring isomorphisms, the separate
unequal-chart Laurent quotient calculation, and the affine-base descent step
are unnecessary: the universal quotient test establishes the ideal equality
directly on the given affine open over an arbitrary base. These steps did not
have separate declared nodes to prune. No unit statement or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The planned chart-coordinate computation can be
replaced below the unit level by the shorter functorial coordinate argument.
No definition or statement repair was needed.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
