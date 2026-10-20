# AlgebraicGeometry.Scheme.Modules.moduleMapIsoLocus_inter_eq_basicOpen_of_free

## Reason

The item is an approved retirement in `coord/retire-items.tsv`. Its upstream twin
already proves a stronger statement, with the unused affineness hypothesis removed.
The duplicate has no remaining Lean importers. Retain the upstream declaration,
withdraw the Sheaf module, and attach the existing DAG node to upstream.

## Old

In `Sheaf.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen`:

```lean
theorem moduleMapIsoLocus_inter_eq_basicOpen_of_free {W : Scheme.{u}}
    {M N : W.Modules} (φ : M ⟶ N) (U : W.Opens) (hU : IsAffineOpen U)
    {I J : Type u} [Finite I] [Finite J]
    (eM : M.restrict U.ι ≅ SheafOfModules.free I)
    (eN : N.restrict U.ι ≅ SheafOfModules.free J) :
    ∃ f : W.presheaf.obj (.op U),
      (U : Set W) ∩ (moduleMapIsoLocus φ : Set W) = (W.basicOpen f : Set W)
```

## New

The Sheaf duplicate is withdrawn. The existing, unchanged declaration in
`WeilConjectures.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen` is:

```lean
theorem moduleMapIsoLocus_inter_eq_basicOpen_of_free {W : Scheme.{u}}
    {M N : W.Modules} (φ : M ⟶ N) (U : W.Opens)
    {I J : Type u} [Finite I] [Finite J]
    (eM : M.restrict U.ι ≅ SheafOfModules.free I)
    (eN : N.restrict U.ι ≅ SheafOfModules.free J) :
    ∃ f : W.presheaf.obj (.op U),
      (U : Set W) ∩ (moduleMapIsoLocus φ : Set W) = (W.basicOpen f : Set W)
```

The old affine statement follows directly from this theorem by ignoring `hU`.
Only the node's Lean attachment changes; its mathematical statement is retained.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen | D8 | Withdrawn duplicate; zero holes. |
| Sheaf.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusCompact | Already retired | Listed former consumer is absent from the current library. |
| WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusCompact | Not adapted | Already imports the upstream twin and supplies the correct arguments. |

No current module imports the withdrawn module. The only current external use of the
public theorem is the upstream compactness module above. No definition changes
meaning, and no target statement or source-library declaration is edited.

## Status

landed 20261020T141307-L-2032756 2026-10-20 (merge of deliver/D8/Sheaf.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen)
