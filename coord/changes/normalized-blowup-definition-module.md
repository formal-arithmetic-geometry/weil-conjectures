# AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup

## Reason

The calculus proof uses `normalizedBlowup_finality`, but the finality statement publicly
imports the calculus solely for `normalizedBlowup` and `normalizedBlowupMap`. This creates
an import cycle. Move the two concrete definitions, unchanged, to a definition-only
module, re-export them through the calculus, and point finality to that module.
This is an interface organization repair, with no mathematical change and no new data.
The definition node `def-trf-normalized-blowup` is reattached to the new module.

## Old

In `Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus`:

```lean
noncomputable def normalizedBlowup {S : Scheme.{u}} (J : S.IdealSheafData) : Scheme.{u} :=
  J.blowup.reducedNormalization

/-- The normalized blowup's structural map is the normalization map followed by the blowup
map. Source: ILO, Expose VIII, 2.2.3 (blueprint: lem-trf-normalized-blowup-calculus). -/
noncomputable def normalizedBlowupMap {S : Scheme.{u}} (J : S.IdealSheafData) :
    J.normalizedBlowup ⟶ S :=
  J.blowup.fromReducedNormalization ≫ J.blowupMap
```

`Sheaf.AlgebraicGeometry.NormalizedBlowupFinality` previously had:

```lean
public import Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus
```

## New

The identical two definitions, including their signatures and concrete bodies, live in
`Sheaf.AlgebraicGeometry.NormalizedBlowup`. The calculus publicly imports that module,
so its importers still see the same constants. Finality imports the definition module
and explicitly imports finite type, integrally closed rings and invertible ideal sheaves,
which its statement already uses. Its declaration is unchanged. All proof imports in
the calculus are private. No source-library file is modified.

## Users

`tools/downstream.py --uses normalizedBlowup` and `--uses normalizedBlowupMap` both list
the first four modules below; the fifth is also a direct calculus importer.
All other transitive importers continue to see the identical definitions and theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.MonoschemeToricRealization | V4 | Unchanged signatures and bodies are re-exported through the same calculus import. |
| Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus | D5 | D5 item; re-export definitions and import finality privately. Its theorem signature is unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedBlowupFinality | unclaimed | Unclaimed; replace its calculus import by the definition module and the three statement imports. Its theorem and proof are unchanged. No current downstream importers. |
| Sheaf.AlgebraicGeometry.ToricMonoidComparison | unclaimed | Unchanged signatures and bodies are re-exported through the same calculus import. |
| Sheaf.AlgebraicGeometry.SmoothFunctorialNormalizedToricDesingularization | unclaimed | Unchanged signatures and bodies are re-exported through the same calculus import. |

The target meanings do not change: both moved definition bodies are verbatim.

## Status

landed 20261023T230629-L-3453249 2026-10-23 (merge of deliver/D5/Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus)
