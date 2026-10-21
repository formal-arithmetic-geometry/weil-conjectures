## What changed

Replaced the proof of CategoryTheory.formalExactProjectionMate with an explicit
categorical calculation following the existing seven-step plan. Naturality of
beta follows from tensor comparison and counit naturality, and naturality of
alpha follows from unit naturality. Local natural transformations package the
comparison, beta, and alpha; Mathlib composition and whiskering instances supply
compatibility with every integer shift. Exactness of composites gives the two
distinguished image triangles, and naturality together with shift compatibility
gives their triangle morphism. The right-unit calculation uses hunit, right-unit
naturality, and the adjunction triangle identity. No signatures, definitions,
public imports, or other modules changed.

## Proved and sorry left

Closed the sole original hole, CategoryTheory.formalExactProjectionMate
(lem-weil-pbc-formal-exact-projection-mate): 1 of 1 proved, with 0 holes added,
0 split off, and 0 sorry left. The final module compiles cleanly through
lcompile.py in 4.6 seconds, with no warnings. The signatures and definitions
are unchanged. Delivery preflight checks axioms independently.

## No longer needed

None. All five planned dependencies are Mathlib leaves and the proof follows
their APIs directly. No imports, nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The existing seven-step proof plan is
realized directly using its five Mathlib-matched dependencies, with no change
to the unit route.

The earlier attempt could not load the compiled Mathlib triangulated-functor
module. On resumption that object was present, but a global-build publication
gate caused repeated busy-service responses. After recovery cleared the gate,
Lean checked the file. Two rewrite matches required explicit, fully typed
counit-naturality equalities; both were repaired. The finished proof needs only
second-input shift compatibility. The fixed first-input hypothesis and its
binder name are retained, with a documented theorem-local unused-variable
linter setting. No launcher scripts or shared repository files were changed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
