## What changed

Restore `Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence` from its quarantine as an
adapter to the unchanged adopted source module. The six constructed overlap definitions
are supplied by a public import, avoiding duplicate declarations. Retain and reprove the
four archived helper theorem signatures: `overlapOpenInclusionPullbackIso_whiskerLeft`,
`overlapOpenInclusionPullbackIso_hom_comp`, `overlapOpenInclusionPullbackIso_inv_comp`, and
`perfectOverlapStageObjectIso_hom_app`.

The first three now follow from the actual restriction adjunctions and the pinned
left-derived counit triangle. The stage-object equation follows from the fixed composition
associativity identity. All auxiliary declarations are private; every auxiliary theorem
is proved, and every auxiliary definition has an explicit construction. The node keeps its
attachment and statement dependencies; its proof route records the canonical constructions
and their compatibility calculations. The unit route is preserved.

Change records: `coord/changes/q2-perfect-overlap-stage-canonical-adapter.md` and
`coord/changes/q2-perfect-overlap-stage-object-normalization.md`. The latter records the
source's different association of the stage-object comparison; the restored component
equation proves its agreement with the archived formula.

Validation: `lcompile.py` compiled the restored module in 57.1 seconds and then compiled
a temporary importer containing all four archived signatures verbatim. Each example applies
the corresponding restored theorem. For each of the four helper theorems, `#print axioms`
lists exactly `propext`, `Classical.choice`, and `Quot.sound`. The source constructions and
counit triangle also pass this axiom check. All three proposed imports pass
`tools/import_direction.py may`. There are no long Lean lines, and the node JSON parses.

## Proved and sorry left

This is a zero-hole definition repair: the archived item has 0 sorries. Holes closed: 0.
Holes added: 0. Holes remaining in the delivery: 0. Split-off statements: 0. All four archived
helper theorems are reproved for the canonical source definitions; they are not counted as
closed holes. No axiom, hollow definition, or arbitrary existence witness is introduced.

## No longer needed

The old descent call and the direct import
`WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent` are not used by this
proof. The old direct imports of `Sheaf.AlgebraicGeometry.PerfectHomTransport`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram`, and
`Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived` are replaced by the canonical
source module's public interface. These are removals of redundant direct imports, not
claims that those source modules can be withdrawn. No node or module is withdrawn; the
quarantined parents and the unit's route are retained.

## Where the brief, the DAG or earlier work was wrong

The rework entry correctly diagnoses an import collision. Simply restoring the old six
bodies would introduce more duplicate source names. Conversely, an empty adapter would
lose four helper equations still used by quarantined consumers. The restored adapter
therefore imports the canonical definitions and proves those equations for them. The node's
old statement also mentions transition helpers already pruned by its earlier recorded
proof origin; this delivery preserves the statement and attachment rather than interpreting
that stale text as authority to withdraw any parent. The identities include identity
inclusions and empty opens: no nonemptiness or extra geometric hypothesis is used.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
