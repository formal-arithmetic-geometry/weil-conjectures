## What changed

Retired `Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex` in favour of its
canonical upstream twin, as required by the human's retirement instruction.
Its only remaining importer, the unclaimed and unused
`Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`, is also retired
in favour of its fully proved upstream twin. Both paths are in `deleted.txt`.
The two existing DAG attachments now identify the upstream modules; the comparison
attachment and proof text use the canonical `exteriorPower` API.
No upstream module is changed and no replacement theorem is postulated.

Validation: a remote audit importing the canonical comparison compiled in 1.6 seconds.
It checked the negative-zero and nonnegative-exterior-power branches and printed
axioms for all three definitions and the comparison theorem: only `propext`,
`Classical.choice`, `Quot.sound`. The current direct-import scan and
`tools/downstream.py --uses` agree that there are no remaining consumers after
these two withdrawals. The canonical comparison import closure has no Sheaf modules.

Change record: `coord/changes/T4-retire-locally-ranked-exterior-complex.md`.

## Proved and sorry left

Definition repair and retirement: zero holes before, zero holes after.
Holes closed: none (0 of 0). Holes added: none (0). Split off: none (0).
No sorry remains in any delivered declaration. The upstream
`AlgebraicGeometry.Scheme.Modules.constantRankExterior_derived_iso` is already proved;
this packet does not claim its proof as new work.

## No longer needed

Withdrawn modules:
- `Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex`.
- `Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`.

The retired complex no longer imports `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`,
`Mathlib.Topology.LocallyConstant.Basic` or
`Mathlib.Algebra.Homology.HomologicalComplex`; the canonical complex obtains its
exterior power from `WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower`.
The retired comparison no longer imports the Sheaf complex,
`WeilConjectures.AlgebraicGeometry.DerivedCategory`,
`Mathlib.Algebra.Category.ModuleCat.ExteriorPower` or
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso`.
The corresponding canonical upstream imports and proof remain intact.
Both nodes are retained and repointed, not deleted. No mathematical dependency
or unit step is pruned. Other modules defining the old exterior-sheaf API are left
to their own retirement items.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a sorry item, but this queue row is a
`retire-first` definition repair with zero sorries. The retirement inventory is
older than the current tree: only the constant-rank comparison remains as a direct
importer, and that comparison has no importers. The canonical upstream construction
uses `exteriorPower`, so retaining the old consumer unchanged would retain the
independent exterior-sheaf construction. Retiring the unused comparison avoids that
API mismatch while preserving its mathematical theorem upstream.

Searches through msearch.py: LeanFinder returned unrelated general cochain and
exterior-power infrastructure, Loogle did not know the project declaration name,
and Mathlib grep returned no exact match. Direct source search found the existing
upstream construction and its complete constant-rank comparison proof.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
