## What changed

Proved `AlgebraicGeometry.Scheme.completedReductionFiniteEvaluation_normalized` in
`Sheaf.Paper.CompletedReductionFiniteEvaluationNormalization`, with its statement,
universes, public imports, and existing docstrings unchanged. Added proof-only
`import all` imports of `CompletedPullbackReduction` and `CompletedTowerPullback`
to reuse their already proved private helpers without changing their visibility.

The coefficient-map equality uses limit projection uniqueness. The four exactness
clauses reuse the completed and levelwise pullback proofs. Naturality is the
naturality field of the composite universal-counit natural transformation. K-flat
invertibility reuses the two existing model-map proofs. Unique existence uses
`completedReductionFiniteEvaluation_exists`, and the selected comparison satisfies
the normalization by that theorem's choice specification. This realizes the
existing DAG plan through its existing Lean proofs, so no DAG route changes or
new nodes are needed.

Searches: LeanFinder queried "universal left derived counit of an exact functor is
an isomorphism" (bounded derived results, no better match); Loogle and remote grep
found `Functor.isIso_of_isLeftDerivedFunctor_of_inverts`. Local searches and reading
both imported modules found that the entire required argument already exists in
the library. The final proof reuses it directly. Remote single-file compilation
passed in 3.2 seconds before removing two unnecessary exploratory options; the
final packet is checked again by the delivery tool.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.completedReductionFiniteEvaluation_normalized`
(node `lem-weil-pbc-derived-finite-evaluation-normalization`).

Added 0 holes. Remaining holes in the item: none. No split-off statements or new
modules. Existing dependencies retain their own proof status; this delivery does
not assert that the entire transitive target closure is free of sorry.

## No longer needed

None. Both original public imports remain. The original dependency argument is
already implemented in the imported modules and is reused; no dependency module
or DAG node is withdrawn. Exploratory copies of helper proofs were removed from
the delivered Lean file in favor of the original private helpers.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The long DAG plan is already implemented
by private helpers and the public existence theorem. Lean's `import all` permits
proof reuse without exposing these helpers publicly or duplicating them.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
