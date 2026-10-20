## What changed

Restored the assigned quarantined module at its original Lean attachment, with
its original bounded-below comparison theorem and all four DAG dependencies.
Removed two sync-orphaned top-level proof bodies and private helpers used only by
the old finite-free, flatness, and finite-push proofs. Those declarations remain
in the upstream library, which this delivery does not edit.

Kept the bounded scalar-basis, reflection, mate and copower argument. Explicit
unfolding of `CondensedQbarDerivedScalarBasis` avoids expensive existential
elaboration, and an explicit family of canonical commutative-object instances
makes the adjunction applications elaborate. The main module compiled in 20.9 s alone and 45.5 s in the consumer-check set.
The scratch consumer compiled in 3.0 s using only the restored public import
and an application of the exact archived theorem signature.
The generic reflection and mate helpers are proved; no data definitions remain.

Updated only the node's proof origin to record the post-sync restoration; the
proof steps, dependencies and Lean attachment are unchanged. Import visibility
and archived consumer review are documented in
`coord/changes/D4-bounded-coefficient-push-sync-restoration.md`.

## Proved and sorry left

This is a zero-hole rework assignment: 0 existing sorries, 0 closed, 0 added,
0 split off, 0 left. Restored the complete proof of
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE`
(node `lem-weil-pbc-condensed-qbar-bounded-push`), with exactly its old signature.
There are no remaining local holes to name. Existing holes in imported library
results are unchanged; no new claim of closing them is made.

## No longer needed

Removed redundant imports:
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`,
`WeilConjectures.ConstructibleSheaf.FreeLifting`,
`WeilConjectures.CategoryTheory.ModuleObjects.Free`, and
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.
The first two remain transitively public through upstream Compatibility; the
last three served the discarded private finite-free pipeline.

The four retained proof dependencies now use plain `import`:
`Sheaf.CategoryTheory.CoefficientPushCopowerCriterion`,
`Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`,
`Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis`, and
`Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers`.
All four named dependency nodes are still used. No DAG dependency, module,
upstream declaration, or unit route is withdrawn. No `deleted.txt` is supplied.

## Where the brief, the DAG or earlier work was wrong

The item is absent from live Lean because it was quarantined, not because it was
withdrawn. Its archive contains zero textual sorries but does not parse: the
sync retained the bodies of the algebraic-closure flatness instance and finite
push instance after removing their headers. The assigned repair is restoration
of the bounded comparison, not a request to prove unrelated upstream holes.
Its existing DAG route is appropriate and unchanged. An upstream all-unbounded
push instance also exists, but this proof retains the bounded scalar/copower
route rather than using that stronger holed statement.

Delivery-tool result: the normal dry run passed compilation and preflight at
`d5fb1fcca02` (CODEX review class). The final push run was interrupted after
roughly fifteen minutes stuck in the delivery cache. Its traceback repeats
`delivery_cache.py:66 -> load -> _load` as the shared tip changes and finally
waits at `delivery_cache.py:52`, `fcntl.flock(... LOCK_EX)`, reached through
`deliver3.py:225`, `cycle_graph`. The first dry run had the same trace after
roughly thirty minutes; a normal retry then produced the successful dry run.
No launcher file, cache, lock or gate was edited or bypassed. No push completed.
The repair and successful consumer-check source remain in this sandbox.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
