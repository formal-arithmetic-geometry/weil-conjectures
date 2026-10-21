## What changed

Restored `Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionEquation` from
its current quarantine source, as assigned by `coord/rework.tsv`.
Replaced exactly two private proof imports:

- `Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit` with
  `WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit`;
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat` with
  `WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`.

The original file fails at line 118 because
`SingleComplexBaseChange.counit_isIso_kFlat` is unknown. The withdrawn Sheaf
provider no longer declares it. The source provider requires `IsKFlatTensor`,
which the matching source bounded-flat theorem supplies. The repaired file
compiles without warnings in 13.5 seconds through `lcompile.py`.

All declarations, signatures, public imports, proof bodies and docstrings
are preserved verbatim. Both new imports pass the import-direction check.
The item node and its attachment, proof, proof dependencies and unit route
stay unchanged because the mathematical argument is unchanged.

Change record:
`coord/changes/Q7-standard-single-flat-counit-union-equation-imports.md`.

## Proved and sorry left

This is a zero-hole restoration repair. The quarantined module already has
zero `sorry`s. Its theorem
`AlgebraicGeometry.standardSingleFlatCounitUnionEquation`
(node `new-pc-standard-single-flat-counit-union-equation`) again compiles from
the declared dependencies. The three existing private categorical helpers
remain proved.

Holes closed: 0 of 0. Holes added: 0. Split-off statements: 0.
There are no remaining `sorry` declarations in the delivered module, and
no other Lean module is delivered. No transitive hole closure is claimed.

## No longer needed

The two obsolete private Sheaf imports listed above are removed from this
module. Their mathematical roles remain necessary and are supplied by the
adopted source APIs. No DAG node or mathematical dependency is pruned.
No declaration, module or archive is withdrawn or deleted.

The unchanged `StandardSingleFlatCounitPresentation` public import and
`StandardSingleFlatCounitUnionTriangles` proof import remain necessary.
The latter supplies the local comparison diagram; the two corrected source
imports respectively supply the pinned counit and its K-flat hypothesis.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a possible proof task, but this assignment is
the listed global-build restoration of an already proved module. The actual
failure is stale proof imports after the source-library consolidation, not
an unproved factorization step. No further decomposition is needed.

The bounded-flat node's current Lean record still names its Sheaf provider,
although its explanatory note mentions the source API. The source theorem
with the same name and the `IsKFlatTensor` conclusion is the provider needed
by the current counit theorem. Neither provider nor node is modified here.

Checked the declared dependency signatures and the unit's realized lists.
Lean Finder and Loogle both find Mathlib's
`CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃`, already used in the
existing proof; Mathlib grep confirms it. No shorter replacement argument
or new geometric lemma is required for this repair.

The live downstream scan finds zero consumers because the parent
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionPresentation` is also
quarantined. Reading that preserved parent and its DAG dependency confirms
that it still calls this theorem. Its statement and import interface are
preserved, and it is not withdrawn.
An additional `lcompile.py --all` check in the item's scratchpad compiled
the repaired equation in 14.8 seconds and the unchanged archived parent in
5.9 seconds, without warnings. These scratch copies are not delivered.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
