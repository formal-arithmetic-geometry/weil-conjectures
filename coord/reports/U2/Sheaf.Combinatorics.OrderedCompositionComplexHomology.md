## What changed

Filled six existing proof holes in
`Sheaf.Combinatorics.OrderedCompositionComplexHomology`, following steps 2--4
of `lem-sfb-ordered-composition-complex-homology`.

The merge proof splits the sum at the skipped index using
`Fin.sum_univ_succAbove`; nonzero natural-coordinate blocks remain nonzero after
addition. The partial-sum proof uses strict increase of finite sums under
inclusion, with the last block witnessing that each vertex is below the total.
Its first block witnesses that each vertex is nonzero.

Moved the existing partial-sum and cumulative-comparison declarations before
the complex constructions. This permits `boundary_squared` to use the existing
`cumulative_comparison` statement: two sign reversals transport the composite to
`ProductChainProperInterval.boundary_squared`, and injectivity reflects zero.
The zero-multidegree case is proved separately by emptiness of every positive
composition basis. The dual square-zero identity follows by evaluation, and
the interval square-zero identity is the original interval identity with its
bottom zero map handled separately.

The complex isomorphism multiplies the comparison in degree n by (-1)^n.
Its degree-zero component is the unique map between zero modules when m is
nonzero; positive components are bijective because their scalar is a unit.
The negative-boundary identity gives the component chain-map equation.
`HomologicalComplex.Hom.isoOfComponents` supplies the inverse, and `mapIso`
gives exactly the required derived-category isomorphism.

All existing declaration signatures, definition bodies, public imports and
docstrings are preserved. The DAG's existing step 3 explicitly gives this
transport argument and step 4 gives the localization argument, so its proof
plan and dependencies are unchanged. No other existing module was edited.

Searches used LeanFinder for the vector-composition/cumulative-chain comparison,
Loogle for the finite-sum splitting identity, and grep both through the search
wrapper and in Mathlib and both project roots. Scalar composition lemmas did
not identify this vector-valued complex. The useful existing ingredients were
the displayed cumulative comparison, the published interval square-zero lemma,
finite-sum order lemmas and Mathlib's component-isomorphism construction.

The delivered file compiles on the server without errors or warnings in 5.3 s.
The edge cases m=0, degree zero, an empty partial-chain index set and r=0
are retained: the first two have explicit proof branches, and the remaining
ones are covered by the finite-sum proofs without a nonempty-coordinate
assumption.

## Proved and sorry left

Closed 6 of the original 8 holes, with no holes added:

- `OrderedCompositionComplex.merge_valid`;
- `OrderedCompositionComplex.partialSums_valid`;
- `OrderedCompositionComplex.boundary_squared`;
- `OrderedCompositionComplex.dualBoundary_squared`;
- `OrderedCompositionComplex.intervalBoundary_squared`;
- `OrderedCompositionComplex.comparison`.

The two original holes left, both attached to
`lem-sfb-ordered-composition-complex-homology`, are:

- `OrderedCompositionComplex.cumulative_comparison`;
- `OrderedCompositionComplex.homology`.

This is a partial delivery. The boundary and complex-isomorphism proofs use
the original, still unproved cumulative comparison; the interval identity uses
the original `ProductChainProperInterval.boundary_squared`. These are the
stated proof obligations of the plan, not new assumptions or split-off holes.
The final homology dimension formula is unchanged and remains unproved.

## No longer needed

Removed unused private imports:

- `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`;
- `Mathlib.LinearAlgebra.Dimension.RankNullity`.

No DAG node or library module is claimed pruned. The rank-nullity, quotient
dimension and dual-rank nodes are still needed by the unfinished homology
argument; removing unused direct imports here does not withdraw those
mathematical obligations. The proper-interval module remains used.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The original declaration order placed
`boundary_squared` before the cumulative-comparison theorem even though its
docstring and DAG step 3 explicitly offer transport through that comparison.
Reordering declarations makes that planned route available without a duplicate
cancellation proof. No statement or definition repair was necessary.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
