# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_map_exists

## Reason

Retirement item in `coord/retire-items.tsv`: the upstream twin proves the same
mathematical map theorem for its `exteriorPower` and `wedge` construction. Retire
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafMapExists` and redirect its only
consumer to `WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafMapExists`.
The two presheaves have definitionally identical section modules. Their
restrictions agree by `exteriorSheafRestriction_existsUnique` and the upstream
`PresheafOfModules.ExteriorPower.map_ιMulti` formula. An explicit presheaf
isomorphism with identity components therefore sheafifies to an isomorphism
preserving wedge sections in both directions. Conjugating the upstream map
with these isomorphisms gives the map required by the unchanged consumer.

No upstream file, target statement, public consumer signature, or definition
is changed. The consumer is unclaimed at preparation time.

## Old

The retired module declared:

```lean
theorem exteriorSheaf_map_exists {X : Scheme.{v}} {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    ∃ e : exteriorSheaf M n ⟶ exteriorSheaf N n,
      ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U)),
        e.val.app (op U) (exteriorSheafSection M n U a) =
          exteriorSheafSection N n U (fun i ↦ f.val.app (op U) (a i))
```

The consumer privately imported
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafMapExists` and applied this theorem.

## New

The node points at the existing, unchanged upstream declaration:

```lean
theorem exteriorSheaf_map_exists {X : Scheme.{v}} {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    ∃ e : exteriorPower M n ⟶ exteriorPower N n,
      ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U)),
        e.val.app (op U) (wedge (M := M) (r := n) (U := U) a) =
          wedge (M := N) (r := n) (U := U) (fun i ↦ f.val.app (op U) (a i))
```

The retired file is listed in `deleted.txt` (the delivery protocol empties it).
`Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt` replaces the
private import by the upstream twin. Five proved private helpers construct the
comparison and transport its map; the public theorem's sole call-site change
is to use `exteriorSheaf_map_from_upstream` instead of the retired theorem.

## Users

The downstream command lists seven modules. The only external textual user of
`exteriorSheaf_map_exists` and the only direct importer of the retired module
is the first row. All remaining rows keep identical source and public types.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt | unclaimed | Adapt private import and proof via the explicit comparison; public signature unchanged; compiled. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | No change; consumes the unchanged local-data theorem. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | No change; public dependency API unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | No change; public dependency API unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | No change; public dependency API unchanged. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | No change; public dependency API unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | No change; public dependency API unchanged. |

## Status

landed 20261020T144253-L-2260279 2026-10-20 (merge of deliver/K8/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafMapExists)
