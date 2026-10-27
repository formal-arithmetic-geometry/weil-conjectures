# AlgebraicGeometry.ProEtale.finiteRingSiteTensorTranspose

## Reason

Restore the quarantined module named by coord/rework.tsv. The live Lean path is
absent; the archive retains all seventeen declarations and the original theorem
hole. Restoring the complete module repairs the missing dependency of the archived
smooth-purity parent. The archive now compiles against the current published build:
the formerly failing dependencies have been repaired independently. No source-level
repair of its definitions is necessary, and no mathematical proof progress is claimed.

## Old

`lean/Sheaf/AlgebraicGeometry/FiniteRingSiteTensorTranspose.lean` is absent.
Its complete source is preserved at
`quarantine/Sheaf/AlgebraicGeometry/FiniteRingSiteTensorTranspose.lean`.
The rework row records the global-build failure after a cluster restoration.

## New

Restore the archive byte for byte at its original Lean path. All seventeen existing
declaration signatures, definition bodies, attributes, visibility, imports, docstrings
and the original theorem proof are preserved. In particular the canonical tensor,
unit, pullback, projection and signed-braiding maps are retained, together with the
unique counit-normalized comparison and both transpose equations. There is no
replacement by an empty module and no withdrawal of the archive.

The existing DAG node lem-pur-finite-ring-site-tensor-transpose retains its Lean
attachment and all dependency edges. The unit route and all target meanings stay
unchanged. No new definition is introduced and no target review is reopened.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose
--allow-missing --uses finiteRingSiteTensorTranspose` reports zero live downstream
modules and zero live textual users. A separate import search in both lean/ and
quarantine/ finds the archived parent below. Zero live importers is not used as a
withdrawal argument. The DAG parent det-sp-finite-general-ring and the smooth-purity
unit remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C3 | Restore all archived declarations. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | No current module-named claim file found | Archived direct importer; its import becomes available again; no source adaptation. |

Validation: the complete archived source compiles on the project server through
lcompile.py in 11.3 seconds, with no compiler errors or warnings. The delivery probe
provides the independent declaration and axiom checks. No consumer is modified.

## Status

landed 20261022T113846-L-321154 2026-10-22 (merge of deliver/C3/Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose)
