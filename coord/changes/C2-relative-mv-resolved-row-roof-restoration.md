# AlgebraicGeometry.relativeMV_resolved_row_roof_comparisons

## Reason

Restore the complete module preserved at the quarantine path in
`coord/rework.tsv` after the failed cluster restore. Its mathematical
proof is complete. Its vertex-normalization dependency has been restored
and retains the statement used by the archived proof. Avoid unpacking
and reconstructing its dependent comparison witnesses in the final step.

## Old

The library path
`lean/Sheaf/AlgebraicGeometry/RelativeMVResolvedRowRoofComparisons.lean`
is absent. The complete source is preserved at
`quarantine/Sheaf/AlgebraicGeometry/RelativeMVResolvedRowRoofComparisons.lean`.
Its proof ended with:

```lean
  obtain ⟨e₁, e₂, e₃, e₁', e₂', e₃', hv₁, hv₂, hv₃, hα, hβ, hγ⟩ :=
    relativeMV_resolved_roof_vertex_normalization f f' g g' hpull K K' φ U V
      r s u₀ hr hs rfl rfl rfl
  exact ⟨_, _, e₁, e₂, e₃, e₁', e₂', e₃', hv₁, hv₂, hv₃, hα, hβ, hγ⟩
```

## New

Restore the original module, preserving every declaration signature,
docstring, import and private construction. Its proof ends with:

```lean
  exact ⟨_, _,
    relativeMV_resolved_roof_vertex_normalization f f' g g' hpull K K' φ U V
      r s u₀ hr hs rfl rfl rfl⟩
```

Keep `schemeOpenModuleAdjunction` and `schemeOpenModuleImageRestriction`
locally irreducible while elaborating the private row-map definition.
Respect their transparency instead of unfolding their concrete transported
functor data. The original row-map body and its three vertex maps are
unchanged; no additional helper is introduced.

Keep the right-derived functors and `RingedSpace.moduleDirectImage` locally
irreducible while elaborating the public theorem. Use the same transparency
settings as the restored vertex-normalization dependency and
`dsimp -proj only` for the statement aliases. This prevents costly unfolding
of concrete functors and row projections. These are elaboration settings;
no mathematical definition changes.

The complete final implementation compiled in 41.0 seconds with no errors
or warnings. The unchanged archived direct consumer compiled in 18.4 seconds
against the restored interface. Its temporary copy is not delivered.
The original archive compiled in 55.5 seconds; intermediate experiments
reached the unchanged 60-second limit before the folding settings were
applied to the private row map as well. No diagnostic options remain.

No hypothesis, conclusion, definition, source-library declaration or target
changes. There are zero `sorry`s before and after restoration.

## Users

`tools/downstream.py --allow-missing --uses` reports no current library
importers, because the item and its parent are quarantined. Direct searches
of the library and quarantine archive find the sole direct consumer below.
It applies the identical theorem with identical arguments and consumes the
same witnesses and equations. Its public interface needs no adaptation.
No archived source or dependency is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRowRoofComparisons | C2 | Restore complete proof and simplify final witness assembly. |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowRoof | unclaimed in shared snapshot (quarantined) | Same public signature; no adaptation. |

## Status

landed 20261021T005727-L-1885776 2026-10-21 (merge of deliver/C2/Sheaf.AlgebraicGeometry.RelativeMVResolvedRowRoofComparisons)
