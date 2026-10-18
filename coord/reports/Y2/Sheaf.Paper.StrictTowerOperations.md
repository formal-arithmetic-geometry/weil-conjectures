## What changed

Filled all four holes in `Sheaf.Paper.StrictTowerOperations`, without changing any
statement or definition. Added the proof-only import
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory` for pointwise exactness.
Updated `def-weil-pbc-strict-tower-operations` proof, proof dependencies and proof origin.

The constant-section comparison proof follows the existing proved private argument in
`ProfiniteCoefficientInverseImage`: uniqueness of left adjoints identifies the specified
map with a natural isomorphism, with no finiteness assumption. Tower exactness follows
from the existing ordinary module exactness instances and Mathlib pointwise preservation.
The ordinary composition comparison is the inverse conjugate of the existing sectionwise
normalized direct-image isomorphism; the equivalence laws and sectionwise extensionality
prove existence and uniqueness. Coefficient transport is `Sigma.ext` applied to the two
specified coherence fields.

Change record: `coord/changes/Y2-strict-tower-proof-import-pruning.md`.
The original sole downstream module `Sheaf.Paper.TateInverseLimitBaseChange` was compiled
unchanged against the delivered module. It is not part of the delivery.

## Proved and sorry left

Closed 4 of 4 holes, all attached to `def-weil-pbc-strict-tower-operations`:

- `AlgebraicGeometry.Scheme.exchangeConstantComparison_isIso`.
- `AlgebraicGeometry.Scheme.exchangeTowerModulePull_exact`.
- `AlgebraicGeometry.Scheme.exchangeModuleComposition_existsUnique`.
- `AlgebraicGeometry.Scheme.StrictTowerRingedSquare.exchangeCoefficients_eq`.

Zero holes remain in the item; zero holes added; zero split-offs. The composition
proof uses the existing stated `proEtaleRingDerivedPullbackComposition`, whose proof
remains a separate existing obligation. This delivery does not claim to close that hole.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`: no intrinsic finite
  coefficient operation is used in arbitrary ring-sheaf strict towers.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`: no scalar-change
  comparison is used; the ordinary operations remain available through `FourCorners`.
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`: the selected derived
  comparison and `proEtaleCanonicalPullbackComposition_existsUnique` are not used.
  The underlying `ProEtaleDerivedPullbackComposition` theorem remains needed and is
  available through `FourCorners` and its ambient ringed exchange import.

The composition proof also does not use that theorem's auxiliary normalized adjunctions,
ordinary pullback comparison, complex comparison or derived/K-flat clauses. It extracts
only the direct-image isomorphism and its sectionwise formula. The ordinary composition
node remains needed; no node or unit realization is withdrawn. The unit route is unchanged.
Global removal of modules depends on the maintainer's import-closure recomputation.

## Where the brief, the DAG or earlier work was wrong

The existing composition docstring proposes identifying three existential normalized
adjunctions with the canonical adjunctions. That identification is unnecessary: conjugate
the already supplied direct-image isomorphism using the canonical adjunctions directly.
This proves the exact original normalization and uniqueness without any new statement.
The item's definition node originally had no proof steps; it now records the implemented
four-part argument. No false statements or definition defects were found.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
