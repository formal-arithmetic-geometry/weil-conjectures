## What changed

Proved all eight existing holes in
`lean/Sheaf/Paper/QuotientPullbackCompositorNormalization.lean` without changing any
existing signature, definition body, public import, or theorem docstring.

The private proofs already in `PerfectProjectionFormula` implement the node's
ordinary and derived composition arguments. A private `import all` reuses
`PerfectProjection.quotientPullback_compositor`,
`PerfectProjection.coefficients_comp`, and
`PerfectProjection.quotientDerivedPullback_compositor`. These independently proved
helpers do not invoke this item or the parent's unfinished projection-formula
statement. The square proof repeats only the short compositor cancellation and
equality transport from the parent's local square calculation. The ordinary
transition calculation follows the parent's proved transition theorem, whose
published result supplies the derived conjunct.

For finite-system maps, applied the constant-sheaf functor to the tower naturality
square, identified the two adjacent quotient-map presentations by quotient
extensionality, and constructed the sectionwise additive module map. The `limMap`
projection equation proves scalar linearity, and sectionwise extensionality proves
uniqueness. Limit projections and constant-comparison naturality prove the completed
ring square.

Ordinary system naturality is proved by transposing through the actual module
adjunction. The restriction comparison is the mate of the specified direct-image
comparison, which is identity on sections. The quotient and system-map section
formulas reduce the assertion to constant-comparison naturality. A private
`import all` of `ProEtaleRingSheafChangeAdjunction` supplies its already proved
`mate_adjunct` and `restrictionPullback_mate` calculations.

Derived system naturality follows from the ordinary square using the published
single-functor normalization for derived composition and natural isomorphisms.
After postcomposing with the invertible restriction/single comparison, its
naturality and the composition identities reduce the equation to the single-functor
image of the ordinary square. Added private proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` and
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor`.
A private local instance specializes the published
`integralCoefficientAbLocallyBijective` at universes `(u, u)`, preventing an
underdetermined larger coefficient universe during instance inference.

The mathematical route of the existing node is unchanged: the existing private
composition proofs already implement its steps 1--6, the explicit finite-system
proofs implement step 7, and compositor cancellation implements step 8. There are
no new statements or DAG nodes, and no node file needs modification.

Validation: compiled the complete file through `lcompile.py` with zero errors and
zero warnings after removing unused imports (19.2 seconds). No source-library file
or other consumer is changed. Existing statements continue to include zero rings,
empty schemes, identity arrows, and level zero (paper exponent one); the proofs add
no nonemptiness, nonzero-ring, properness, or finiteness assumptions.

## Proved and sorry left

Closed 8 of 8 original holes, all in namespace
`AlgebraicGeometry.Scheme.QuotientPullbackNormalization` and all attached to
`lem-weil-pbc-quotient-pullback-compositor-normalization`:

- `systemSheafMap_naturality`
- `systemModuleMap_existsUnique`
- `systemRingMap_square`
- `system_naturality` (both ordinary and derived conjuncts)
- `ordinary_composition`
- `derived_composition`
- `transition_naturality` (both ordinary and derived conjuncts)
- `cartesian_square`

No holes remain in this module. No holes were added and no results were split off.
The already stated dependencies retain their existing proofs and hole status.

## No longer needed

Removed the following direct private imports:

- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`

Their interfaces or lower-level machinery are already available through the
retained dependencies. In particular, the K-flat comparison is already proved
inside the published canonical normalization used by the parent's private derived
composition proof; it is not reproved here. This removes redundant import edges,
not the underlying mathematics. No module is withdrawn and no DAG dependency is
claimed globally unnecessary: the original mathematical proof dependencies remain
used through the reused proofs and normalization results. The public imports are
unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or source correction was needed. The stage-2 reader's
advisory already identifies the composition statements as public versions of
private, proved parent results. Those results can be reused directly using Lean's
private `import all`, without changing their visibility or copying their long
proofs. The current parent has no Lean import of this item, so this introduces no
Lean import cycle. Searches via `msearch.py` (Loogle, LeanFinder, grep), together
with local source searches, found the existing private composition proofs and the
published exact-derived single-functor API; Mathlib itself does not state the
completed-quotient specialization.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
