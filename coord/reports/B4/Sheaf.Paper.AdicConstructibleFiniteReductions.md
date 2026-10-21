## What changed

Restored the quarantined item from the current `coord/rework.tsv` archive and preserved its
public declarations, signatures, definitions, coefficient universes, and existing dependencies.
Completed the normalized derived tensor unit, derived scalar associativity, and derived
scalar/pullback comparison. The unit theorem and its selecting definition move below the
existing private ordinary adjunction so the proof can use that adjunction.

The unit comes from the resolving-class derived adjunction, transported to the fixed universal
scalar-extension pair. The associator is the universal lift of the composite computation
counit and ordinary balancing. The scalar/pullback square compares both composites to the
derived pullback for the composite structural ring map. All uniqueness proofs use a flat-term
K-flat resolution, cancellation of computation isomorphisms, and localization naturality.
The scalar/pullback argument is written for abstract small sites and supplied algebraic
inverse-image and derived universal data to avoid repeatedly unfolding chosen constructions.
The cancellation argument is proved for abstract categories before specializing to sheaves.

Added private proof imports of
`Sheaf.CategoryTheory.DerivedCategory.ResolvingAdjunction`,
`Sheaf.Paper.KFlatRingedToposPullback`, and
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`.
Updated the existing node's proof, proof dependencies, and proof origin to record these routes.
No public import or non-theorem body changes; no other module is adapted.
The complete module compiles without warnings through `lcompile.py` (52.1 seconds).

## Proved and sorry left

The archive starts with five holes. Three existing holes are closed:

- `AlgebraicGeometry.Scheme.adicFiniteUnit_existsUnique`.
- `AlgebraicGeometry.Scheme.adicFiniteExtendComp_existsUnique`.
- `AlgebraicGeometry.Scheme.adicFiniteComparison_existsUnique`.

Two original holes remain, both attached to
`lem-sfb-adic-constructible-finite-reductions`:

- `AlgebraicGeometry.Scheme.adicFiniteOrdinaryComparison_existsUnique`.
- `AlgebraicGeometry.Scheme.adic_constructible_finite_reductions`.

No holes are added or split off. The three ordinary normalization theorems proved in the
archive remain proved. The derived comparison uses the existing ordinary comparison theorem;
this is an ordinary dependency, not a new hole or a restatement of the derived result.
The main theorem retains its complete original statement and natural-language argument.

## No longer needed

None. No module is withdrawn and no node is pruned. The unfinished main theorem still needs
its recorded route, so the archive's dependencies are preserved. The new completed proofs use
only the three additional proof imports listed above and the existing interfaces.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined, not withdrawn: its missing live source must be restored from the
archive named by `coord/rework.tsv`. That archive compiles against the current dependencies.
The current B4 return contains only the older upstream-sync notice; no numbered repair points
for this item are outstanding there.

The existing node did not explicitly record the normalized resolving-class derived-adjunction
interface needed for the scalar unit, or the independent-coefficient tensor comparison used
to translate the two flatness predicates. Those existing nodes are now recorded as proof
dependencies. The unit route and every mathematical statement are unchanged.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
