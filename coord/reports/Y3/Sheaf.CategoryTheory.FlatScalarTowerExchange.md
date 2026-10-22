## What changed

Proved `CategoryTheory.FlatScalarTowerExchange.flatScalarTowerExchange`. Faithfulness
of underlying sheaves proves the ordinary square, a degreewise calculation passes to
complexes, and `Localization.natTrans_ext` detects equality in the derived category.
The given adjunct normalization yields the counit equations; naturality and Mathlib's
mate-counit identity prove the mate equality and its explicit transpose. The categorical
calculation lemmas are private, complete, and in the assigned module.

Retained all eight original normalized-derived fields and all four edge-normalization
conditions. Named actual functor constructions, canonical inherited instances and
shared normalization predicates avoid costly dependent conversions. All new explicit
helpers are attached to the existing node; no new mathematical claim is assumed. The original theorem's statement text and universes
are unchanged. The complete definition changes and equivalences are recorded in
`coord/changes/flat-scalar-tower-normalization.md`; no downstream Lean module needs
adaptation. No target or adopted source-library declaration changes.

## Proved and sorry left

Closed: `CategoryTheory.FlatScalarTowerExchange.flatScalarTowerExchange`, one of one
original holes. Added: none. Remaining: none. Split off: zero. The complete candidate
compiled cleanly through `lcompile.py` in 22.4 seconds. A separate complete-file
`#print axioms` check returned exactly `propext`, `Classical.choice` and `Quot.sound`.
Delivery also runs its required compile and preflight. No axiom, hollow definition,
new theorem assumption or admitted private helper is added.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.DiagramSiteRealization` and
`Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`. The required structures are
already supplied as corner and derived-edge data, so the proof does not use
`lem-weil-pbc-diagram-site-realization` or
`lem-pc-pre-derived-adjoint-functors-general`; their statement dependencies remain.

Replaced public import `Sheaf.CategoryTheory.FlatRingedDiagramRestriction` by its
statement interface `Sheaf.CategoryTheory.FlatRingedDiagramRestrictionDefs` and the
complex-adjunction API `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
The existence theorem `lem-weil-pbc-flat-ringed-diagram-restriction` is not reapplied:
the hypotheses already fix p, d and every normalization equation. It is removed from
proof dependencies and retained as a statement dependency specifying those comparisons.
Existing users of its theorem and its own proof dependencies remain intact.

No module, declaration or DAG node is withdrawn. The unit's statement and route remain.
The localization dependency is a Mathlib leaf whose declared API includes
`Localization.natTrans_ext`, used directly in the proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or missing mathematical step was found. The original dependent
record transports and repeated inherited instances were costly to compare in Lean.
The equivalent interfaces address that cost while retaining every condition. The node
now records the actual faithful-underlying-sheaf, localization and mate calculation,
and attaches the new explicit helpers to the existing statement node.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
