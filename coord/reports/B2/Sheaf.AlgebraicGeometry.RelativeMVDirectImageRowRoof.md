## What changed

Restored `Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowRoof` from the complete
archive specified by `coord/rework.tsv`. Preserved its public theorem
`AlgebraicGeometry.relativeMV_direct_image_row_roof`, all imports and docstrings,
and both private helper signatures. The public theorem signature is textually
identical to the archive.

The proof retains the normalized concrete-row comparison from
`relativeMV_resolved_row_roof_comparisons`. It proves all four exactness
conditions from the degreewise splitting of injective Mayer--Vietoris rows and
preservation of splittings by additive functors. The private exactness helper
now eliminates the `Nonempty` splitting witness directly; the public proof
reduces statement aliases with projection reduction disabled. No mathematical
statement or definition changes.

Change record:
`coord/changes/B2-relative-mv-direct-image-row-roof-restoration.md`.
The sole direct archived consumer is
`Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore`; its original source
compiles against the restored interface without adaptation.

Validation through `lcompile.py`: the final item compiled in 15.0 seconds,
exit code 0, with no errors or warnings; the unchanged consumer compiled in
16.3 seconds against the locally compiled item. A separate axiom probe reports
only `propext`, `Classical.choice` and `Quot.sound` for the public theorem.
The theorem signature matches the archive verbatim and every Lean line has
at most 100 characters. The delivery contains only the restored item, change
record and report; consumer and axiom probes are not delivered.

## Proved and sorry left

Assigned zero-hole restoration. Holes closed: none (0 of 0).
Holes added: none. Split off: none. Sorries left: none.
`AlgebraicGeometry.relativeMV_direct_image_row_roof` and the private helpers
`mapped_split_row_shortExact` and `mv_row_degreewise_split` are fully proved.
The public theorem has no dependency on `sorryAx`.

## No longer needed

No imports, nodes or modules are pruned. Both public imports and the proof
import of `RelativeMVResolvedRowRoofComparisons` remain necessary. The
quarantined parent dependency is preserved. No declaration is withdrawn and
no proof obligation is split off.

## Where the brief, the DAG or earlier work was wrong

The operative assignment is the restoration in `coord/rework.tsv` after a
failed cluster restore, rather than an open proof hole. The module is preserved
in quarantine and already contains a complete proof. There is no item-specific
return in `coord/returns/B2.md` in the shared snapshot.

Searches of `dag/nodes`, `dag/units`, both Lean roots and quarantine by module,
declaration and blueprint identifier find no DAG attachment for the archived
`lem-pc-relative-mv-direct-image-row-roof` tag. The immediate parent's existing
DAG record describes the resolved rows and strictification, but predates this
concrete roof decomposition. The same missing attachment is noted for the
restored comparison dependency in its C2 report. This delivery preserves the
archived tag and dependencies and changes no route; it does not invent a
replacement node or obligation.

All three required `msearch.py` searches ran. LeanFinder returned
`HomologicalComplex.shortExact_of_degreewise_shortExact` and
`CategoryTheory.ShortComplex.Splitting.map`, already used by the proof. The
Loogle query with an unqualified identifier was not recognized; grep confirmed
the degreewise exactness and injective splitting API. Direct library searches
found no shorter replacement for the specialized roof theorem. Inspection of
the Mathlib declarations confirms that additivity suffices to preserve split
rows: no exactness assumption on arbitrary direct image is introduced. The
construction retains the cover assumption and applies to empty or repeated
opens, zero coefficients and zero maps.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
