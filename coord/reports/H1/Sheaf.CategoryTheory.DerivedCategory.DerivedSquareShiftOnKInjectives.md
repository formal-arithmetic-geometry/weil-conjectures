## What changed

Proved `CategoryTheory.derivedSquare_shift_on_kinjectives` in
`Sheaf.CategoryTheory.DerivedCategory.DerivedSquareShiftOnKInjectives`, with its
statement and both computation-map definitions unchanged. Added a private proof
import of `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift` for the proved
criterion `NatTrans.CommShift.of_whiskerLeft`.

Two proved private helpers implement cancellation of a shift-compatible composite
and extension of compatibility from K-injectives along resolution maps. The main
proof forms the two computation natural transformations with associators, uses
the normalization to identify their composites, cancels the left computation map
on shifted K-injectives, and descends to all derived objects. The representative
formula follows directly from normalization and naturality; the termwise and
signed differential clauses follow by component calculation and additivity.
The node's proof records this implementation. No public interface changes, new
nodes, or consumer adaptations.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.derivedSquare_shift_on_kinjectives`
(node `lem-weil-pbc-derived-square-shift-on-kinjectives`).
Holes closed: 1. Holes added: 0. Sorries left: none. No split-off statements.
Both private helpers are proved. The complete module compiled cleanly through
`lcompile.py` in 4.9 seconds, with no warnings.

## No longer needed

None. No existing imports were removed, and all three declared proof dependencies
remain used: exact-functor factorization and its shift compatibility,
K-injective stability under every integer shift, and localization/essential
surjectivity of the abstract derived category. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The implementation extends the units' shift
compatibility from K-injectives by naturality before composing the computation
maps. After the same extension for the precomposed comparison, essential
surjectivity of Q suffices for the final descent; a separate choice of a
K-injective representative of every derived object is unnecessary.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
