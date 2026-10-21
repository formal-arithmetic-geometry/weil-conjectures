# CategoryTheory.DecreasingFiltration.stableSubquotient_at_bounds

## Reason

The assigned queue entry and `coord/retire-items.tsv` list retirement of the Sheaf
module in favor of `WeilConjectures.CategoryTheory.FilteredStableSubquotient`.
The assigned module has zero holes. The existing upstream theorem has exactly
the same signature and complete proof, including the private equality helper.
Current providers have already been unified, so the old DIFFERENT inventory
no longer describes a difference between the current declarations.

## Old

`Sheaf.CategoryTheory.FilteredStableSubquotient` supplied:

```lean
theorem stableSubquotient_at_bounds
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K)
    (p n r : ℤ) (hr : 1 ≤ r)
    (hupper : L.complexStep (p + r) (n + 1) = ⊥)
    (hlower : L.complexStep (p - r + 1) (n - 1) = ⊤)
    (hBZ : L.complexBoundaries p n r ≤ L.complexCycles p n r) :
    Nonempty (cokernel (Subobject.ofLE _ _ hBZ) ≅
      (L.homologyFiltration n).gradedPiece p)
```

## New

Withdraw `lean/Sheaf/CategoryTheory/FilteredStableSubquotient.lean` through
`deleted.txt`. The existing upstream module supplies the exact same declaration
and complete proof above. Reattach the existing node
`lem-sp-filtered-stable-subquotient-at-bounds` to that upstream module and file;
keep its declaration, statement, proof, proof dependencies, and parent edges.
No source-library file changes. No statement or definition of a target changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredStableSubquotient | M3 | Retire the duplicate; its theorem remains upstream. |

`tools/downstream.py` finds zero downstream modules, including with `--direct`.
The `--uses` scan lists only the duplicate itself. Searches of active and
quarantined Lean sources find no direct importers. The former consumer
`Sheaf.CategoryTheory.DegreewiseFilteredStableQuotient` is absent; its upstream
replacement already imports the upstream stable-subquotient module. The DAG
parent `lem-sp-degreewise-filtered-stable-quotient` retains this node as its
proof dependency and is already attached to that upstream consumer. This is
replacement by an identical proved declaration, not withdrawal of the result.
The unit `sk-prop-av-pqf-finite` has no realized slot for this node; its route
and every parent dependency remain unchanged.

## Status

landed 20261021T024152-L-3040755 2026-10-21 (merge of deliver/M3/Sheaf.CategoryTheory.FilteredStableSubquotient)
