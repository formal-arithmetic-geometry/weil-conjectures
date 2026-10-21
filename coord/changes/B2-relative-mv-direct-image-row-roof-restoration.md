# AlgebraicGeometry.relativeMV_direct_image_row_roof

## Reason

Restore the complete module preserved at the quarantine path in
`coord/rework.tsv` after the failed cluster restore. The dependency
`Sheaf.AlgebraicGeometry.RelativeMVResolvedRowRoofComparisons` has been restored
and supplies the same normalized concrete-row comparison used by this proof.
The operative repair is restoration of the missing library module; its archive
has zero holes.

## Old

The library path
`lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRowRoof.lean` is absent.
Its complete source is preserved at
`quarantine/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRowRoof.lean`.
The archived private exactness helper contains:

```lean
  let s := Classical.choice (hA n)
  exact (s.map F).shortExact
```

The archived public proof starts with:

```lean
  classical
  dsimp only
```

## New

Restore the entire archived module with its public theorem signature,
docstring, imports, private helper signatures and mathematical route unchanged.
The degreewise exactness helper eliminates its splitting witness directly:

```lean
  obtain ⟨s⟩ := hA n
  exact (s.map F).shortExact
```

The public proof reduces its statement aliases without reducing projections:

```lean
  classical
  dsimp -proj only
```

No definition, hypothesis, conclusion, source-library declaration or target
changes. The normalized comparison theorem supplies the same row maps, six
vertex isomorphisms, three invertible denominators and three equations. The
cover and degreewise injectivity give split Mayer--Vietoris rows; additive
functors preserve their splittings and therefore their short exactness.

The restored implementation compiled in 15.0 seconds, with no errors or
warnings. The unchanged archived direct consumer compiled against it in
16.3 seconds. A separate `#print axioms` probe reports only `propext`,
`Classical.choice` and `Quot.sound` for the public theorem. Test sources are
not delivered. There are zero holes before and after restoration.

## Users

`tools/downstream.py --allow-missing --uses` finds no current library importers
because the item and its parent are quarantined. Direct searches of both
`lean/` and `quarantine/` find the sole direct consumer below. Its original
application compiles with the same arguments, witnesses and equations; no
consumer adaptation is needed. No archive or dependency is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowRoof | B2 (assigned rework) | Restore complete proof; simplify witness elimination and statement reduction. |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore | unclaimed in shared snapshot (quarantined) | Identical public interface; original consumer compiles unchanged. |

## Status

landed 20261021T012349-L-2179951 2026-10-21 (merge of deliver/B2/Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowRoof)
