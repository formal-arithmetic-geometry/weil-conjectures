# AlgebraicGeometry.generatingSections_pair

## Reason

Repair of the return on delivery c3cdf37bf2a: the assigned module repeated this
proved theorem and its private native-map comparison from
`Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed`. The existing pair theorem
was private and could not be imported. Expose it in its current module, preserve
its proof, and import that module privately in the assigned module. Remove both
duplicate private proofs from the assigned module. The native-map comparison
stays private and unchanged in its original module.

`CompleteLinearSystemClosed` is unclaimed: neither its module claim nor its node
claim exists. This is the interface repair explicitly requested by the return,
not a forced adaptation of another group's item.

## Old

```lean
private theorem generatingSections_pair
    {Y S : Scheme.{u}} {I : Type u} [Finite I] (g : Y ⟶ S)
    (L : Y.Modules) [L.IsInvertible] (s : I → L.sections)
    (hgen : Epi (L.freeHomEquiv.symm s)) :
    ∃ ε : twistRestrict (homOfGeneratingSections I g L s hgen) 1 ≅ L,
      ∀ i, ε.hom.app _ (pullbackSection _ (twistOneSection I S i)) =
        L.presheaf.map (homOfLE (le_top :
          homOfGeneratingSections I g L s hgen ⁻¹ᵁ ⊤ ≤ ⊤)).op
            ((s i).val (Opposite.op ⊤))
```

## New

```lean
theorem generatingSections_pair
    {Y S : Scheme.{u}} {I : Type u} [Finite I] (g : Y ⟶ S)
    (L : Y.Modules) [L.IsInvertible] (s : I → L.sections)
    (hgen : Epi (L.freeHomEquiv.symm s)) :
    ∃ ε : twistRestrict (homOfGeneratingSections I g L s hgen) 1 ≅ L,
      ∀ i, ε.hom.app _ (pullbackSection _ (twistOneSection I S i)) =
        L.presheaf.map (homOfLE (le_top :
          homOfGeneratingSections I g L s hgen ⁻¹ᵁ ⊤ ≤ ⊤)).op
            ((s i).val (Opposite.op ⊤))
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed --uses
 generatingSections_pair nativeHom_eq_generatingSections` reports zero current
importers and only the defining module's internal calls. The declaration type,
proof and all existing public imports remain identical. Exposing the proved
lemma adds an API without changing any definition or target meaning. No
existing consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed | unclaimed | Expose the existing pair theorem; its internal calls and proof are unchanged. |
| Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion | R2 | New private proof import; uses the existing pair theorem at all three call sites, removing both duplicate helpers. |

The complete-linear-system node's Lean declaration list now includes the exposed
helper. The assigned node records the shared pair dependency; only the universal
pair helper is used, not the complete-linear-system closedness theorem. Its unit
route is preserved. There is no import cycle, as checked by
`tools/import_direction.py may`.

## Status

landed 20261023T131745-L-2147605 2026-10-23 (merge of deliver/R2/Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion)
