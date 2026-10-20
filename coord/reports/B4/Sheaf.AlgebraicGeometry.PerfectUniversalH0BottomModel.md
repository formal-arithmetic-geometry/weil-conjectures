## What changed

Restored `Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel` from its
quarantine archive and adapted its retired Sheaf derived-pullback imports to the
adopted `WeilConjectures` modules. The complete archived proof is retained, with
the prior elaboration repairs for monomorphism transport, restriction universes,
derived-comparison factor types, and zero-map evaluation. The public theorem
signature, docstring, definition interfaces, and DAG attachment are unchanged.
No source-library file is edited.

The module compiles through `lcompile.py` with no warnings. The delivery is a
zero-hole restoration rather than a new split or theorem decomposition.

Change record: `coord/changes/B4-perfect-universal-h0-bottom-model-restore.md`.

## Proved and sorry left

The item had zero `sorry`s in its quarantined source and has zero `sorry`s in the
delivered module. Holes closed: 0 of 0. Holes added: 0. Split off: 0. The public
`AlgebraicGeometry.Scheme.perfect_universalH0_bottom_model` theorem and all its
private helpers retain complete proofs. No new declaration is added.

## No longer needed

The retired imports `Sheaf.AlgebraicGeometry.DerivedPullback` and
`Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology` are replaced by their
adopted upstream counterparts. No mathematical proof dependency is pruned: the
finite-free residue model, derived open-pullback homology comparison, locally
free module interface, free-complex API, and square-matrix Mathlib result remain
used. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item was absent from `lean/` because the upstream synchronization quarantined
it after an import collision; the quarantine archive was not a withdrawn
mathematical result. Its archive already contained the full proof. The current
repair therefore restores that proof while resolving the adopted import API and
its resulting elaboration issues. The existing node
`lem-sc-perfect-universal-h0-bottom-model` accurately describes the theorem and
proof route, so no node statement or dependency field changes.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
