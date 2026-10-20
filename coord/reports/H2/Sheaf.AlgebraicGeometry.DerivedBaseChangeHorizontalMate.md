## What changed

Restored `lean/Sheaf/AlgebraicGeometry/DerivedBaseChangeHorizontalMate.lean` from its
quarantine archive, preserving all declarations, imports, proofs and the existing
DAG attachment. Added the explicit module-value universe `.{u}` to
`SheafOfModules` in the section hypothesis at line 177. This matches the pinned
derived-category and relative-Mayer--Vietoris interfaces.

The archived source reproduces the listed `u + 1 = u` error. The repaired module
compiles cleanly through `lcompile.py` (16.5 s). A separate scratchpad compilation
of the repaired module followed by the unchanged archived direct consumer
`Sheaf.AlgebraicGeometry.DerivedBaseChangeSourceTransport` also passes (14.9 s and
25.7 s respectively). No consumer adaptation is necessary.

Change record: `coord/changes/H2-horizontal-mate-sheaf-universe.md`.

## Proved and sorry left

The assigned repair has zero textual holes before and after: 0 closed, 0 added,
0 split off, 0 remaining. The complete existing proofs of the private generic
`horizontal_mates`, private `pullback_source_square`, private `baseChange_eq`, and
public `AlgebraicGeometry.schemeDerivedBaseChange_horizontal_mate` are retained.
The public theorem realizes
`new-lem-pc-derived-base-change-horizontal-mate`. There are no new declarations,
new assumptions or definitions in this delivery.

## No longer needed

None. No import, module, node, declaration or proof dependency is pruned. The
restored theorem still uses the pinned base-change construction and pullback
composition coherence. Both its Lean attachment and all parent dependencies
are preserved.

Searches through the required `msearch.py` interfaces found Mathlib's generic
`CategoryTheory.mateEquiv_hcomp`, plus generic derived-adjunction and Kan-extension
results, but no replacement for the pinned scheme-derived identity. The upstream
mate twin has the same complete proof and already specifies this universe. The
delivery repairs the quarantined Sheaf module without importing another twin
and its duplicate dependency environment.

## Where the brief, the DAG or earlier work was wrong

The queued item is a compilation repair, not a theorem with an unfinished proof.
The archive's omitted `SheafOfModules` universe makes its section hypothesis
ill-typed after the upstream sync. An explicit `.{u}` repairs the actual recorded
defect; the mathematical mate identity and its existing DAG proof plan need no
change. The original quarantine archive is not withdrawn or edited.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
