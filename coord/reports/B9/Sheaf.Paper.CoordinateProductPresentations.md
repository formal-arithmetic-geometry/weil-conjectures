## What changed

Filled all three theorem holes in `Sheaf.Paper.CoordinateProductPresentations`,
without changing any existing theorem signature, attribute, or import.
A proved private helper `support_factors_iff` characterizes factorization through
an iterated coordinate intersection by factorization through every listed divisor.
Its proof is induction on the list using the pullback universal property.

`permutedSupportIso_existsUnique` uses the inverse permutation to show both lists
contain every coordinate, constructs comparison maps, and proves they are inverse
by cancellation against the closed intersection immersions. It then composes with
the existing `supportIso_existsUnique` for the standard list. Uniqueness is
cancellation against the closed zero section. The empty list and rank zero are
included in the same proof; the factorization helper also allows repeated entries
and arbitrary nonreduced or empty bases.

`coordinateRootComparison_existsUnique` uses the existing degree-one
`twistComparison`, heterogeneous reflexivity, and `eq_of_heq`.
`coordinateBoundaryType_eq` is definitional reflexivity.
The node's proof, proof dependencies, and proof origin now describe these proofs.

The existing `coordinateRootDerived` and `coordinateRealizeRootBoundary` definitions
compose the same comparisons through local helpers for generic functors commuting with shifts. This avoids
expanding the exact derived comparison during kernel conversion. Their original
binders and mathematical values are preserved, with definitionally identical
result types now annotated explicitly. The change record is
`coord/changes/B9-coordinate-root-derived-generic.md`. The sole downstream module,
`CoordinateSectionProductRecursion` (Y8), requires no adaptation.

Validation: the complete final module compiled through `lcompile.py` in 25.3
seconds, exit code 0, with no warnings or errors. All profiling options were
removed. The delivered Lean source contains no `sorry`.

## Proved and sorry left

Closed 3 of 3 original holes (namespace
`AlgebraicGeometry.ProEtale.AffineZeroPurity`):

- `permutedSupportIso_existsUnique`.
- `coordinateRootComparison_existsUnique`.
- `coordinateBoundaryType_eq`.

All three belong to `def-pur-coordinate-product-presentations`.
Zero holes remain in the item; zero holes are added or split off elsewhere.
The support proof uses the already stated `supportIso_existsUnique` of
`def-pur-affine-space-thom-map`; its pre-existing proof hole is unchanged.
The private factorization helper is fully proved.

## No longer needed

None. No imports, nodes, modules, or declared dependencies are removed.
The original node had no proof steps or proof dependencies. The existing standard
support identification remains needed; the permutation argument avoids a second
coordinate-ring quotient computation.

## Where the brief, the DAG or earlier work was wrong

The definition node originally had an empty proof plan despite the three named
normalization theorem holes. It now records their actual arguments. No false
statement, target change, or unit-route change was necessary. The original
shifted comparison required the performance repair recorded above to compile
under the fixed file limit.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
