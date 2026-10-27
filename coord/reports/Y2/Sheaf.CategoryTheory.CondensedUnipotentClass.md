## What changed

Filled the seven theorem proofs in `Sheaf.CategoryTheory.CondensedUnipotentClass`.
Restriction and coefficient change are constructed on all profinite test objects.
Private proved helpers provide the sectionwise linear maps, biproduct coordinate
identities and joint injectivity. The action is the explicit linear shear
`z ↦ z + inl(a(g) * second(z))`; its coordinates prove uniqueness, naturality,
equivariance and the positive cocycle formula. Exactness follows from Mathlib's
split biproduct short exact sequence and the existing `forgetExact` theorem.
Public signatures, definitions, instances and imports are unchanged.
A declaration-scoped linter option suppresses the unused bound name in the
pre-existing `∃! d : UnipotentAction a, True` statement.
The node now records the implemented proof. No other module is edited. The file compiles in 15.5 seconds; the delivery
preflight performs the final compile and axiom checks.

## Proved and sorry left

Closed 7 of 7 existing holes, all in namespace
`CategoryTheory.CondensedDerivedRestriction`:

- `restrictCharacterExist`
- `unipotentActionExist`
- `extensionMaps`
- `extensionZero`
- `extensionExact`
- `extensionPositive`
- `coefficientCharacterExist`

All belong to node `def-sfb-condensed-unipotent-class`.
No holes remain in the item; no holes are added or split off.
The proof uses the existing `forgetExact` dependency, whose separate proof is
outside this item. The derived class definitions retain their existing dependencies.

## No longer needed

None. No import, declared dependency, node or module is withdrawn. The original
node had no proof steps or proof dependencies to prune. Its three statement
dependencies are retained, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The node was a definition node with an empty proof plan. Its theorem docstrings
provided the construction argument, now realized directly in Lean.
The historical quarantine row is stale for the item source: the assigned module
is present in the shared library and is preserved, with all public declarations.
No mathematical statement or definition repair was necessary.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
