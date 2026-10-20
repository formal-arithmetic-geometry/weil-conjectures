# SheafOfModules.existsUnique_hom_of_cover

## Reason

Retire the local duplicate in favor of the proved upstream theorem, as assigned
by `coord/retire-items.tsv` and the human hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. The assigned module has zero holes.
Repair returned head `6814f6bed` against current `sheaf-dag`: preserve the completed
finite-free-dual proof and migrate the new finite-etale consumer. No upstream
source or target statement changes.

## Old

Module: `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.

```lean
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
```

The local theorem's pullback instance binder was:

```lean
[∀ (V : C) (g : V ⟶ U) (i : I), HasPullback g (f i)]
```

## New

Withdraw the local module. Its existing DAG node refers to the unchanged proved
`SheafOfModules.existsUnique_hom_of_cover` in
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
The upstream theorem requires only:

```lean
[∀ i j : I, HasPullback (f i) (f j)]
```

The old hypothesis supplies these instances with V = Uᵢ i and g = f i.
The conclusion and all other hypotheses agree. The mathematical gluing statement
and proof route are retained. No declaration of the adopted source tree is removed.

Remove the unused private import from the conormal and finite-etale consumers.
Replace the private import in the restored self-Tor consumer by the upstream twin;
the existing theorem application compiles with the weaker pullback hypothesis.
The conormal and finite-etale proof bodies do not apply the theorem, so those
consumers need no replacement import.
The former finite-free-dual consumer now has a proved body and no gluing import;
its current version is preserved verbatim rather than overwritten by the stale
sandbox copy.

## Users

The current source scan finds three direct consumers; the self-Tor consumer was
restored while the repaired submission was being checked. The conormal and
finite-etale consumers are unclaimed; A9 holds the self-Tor
consumer. Other consumers in the retirement queue have already migrated or retired.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange | unclaimed | Remove the unused private import of the withdrawn module. |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleLocalizationComparison | unclaimed | Remove the unused private import of the withdrawn module. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback | unclaimed | Preserve current source verbatim; recompile, with no delivery change. |
| Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso | A9 | Replace the private import by the upstream twin; preserve its complete proof and gluing application verbatim. |

No adapted signature, definition, proof body, attribute, visibility, or public
import changes. Both existing consumer holes remain unchanged.

## Status

landed 20261020T153025-L-2865044 2026-10-20 (merge of deliver/X5/Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing)
