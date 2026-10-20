# AlgebraicGeometry.Scheme.exists_gluedCompatibleImmersionCharts

## Reason

Retire the unused Sheaf copy in favour of the proved official source-library theorem,
as requested by the stage-3 retirement queue. The old copy and upstream declare the
same name. Upstream has removed the unused `hU` cover hypothesis. Its theorem therefore
proves the old statement by direct application; no mathematical argument is lost.

The current repository has no direct importers of the Sheaf module. Its former
consumer LocalImmersionLocus already imports and applies the upstream version without
`hU`. No source-library file is edited.

## Old

In Sheaf.AlgebraicGeometry.CompatibleImmersionGluing:

```lean
theorem exists_gluedCompatibleImmersionCharts (S : Scheme.{u})
    (U : S → S.Opens) (hU : ∀ s : S, s ∈ U s)
    (W : S → Scheme.{u}) (j : ∀ s : S, W s ⟶ (U s).toScheme)
    (hj : ∀ s : S, IsImmersion (j s))
    (hcompat : ∀ (i k : S) {T : Scheme.{u}}
      (a : T ⟶ (U i).toScheme) (b : T ⟶ (U k).toScheme),
      a ≫ (U i).ι = b ≫ (U k).ι →
      ((∃ h : T ⟶ W i, h ≫ j i = a) ↔ (∃ h : T ⟶ W k, h ≫ j k = b))) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ S),
      ∀ i : S, ∃ e : W i ⟶ Z, IsPullback (j i) e (U i).ι q
```

The module also contains two private proved helpers, compatibleImmersion_openOverlap
and exists_gluedMonoOpenAtlas.

## New

Withdraw lean/Sheaf/AlgebraicGeometry/CompatibleImmersionGluing.lean, leaving the
historical empty module produced by the delivery tool. Point the DAG attachment to
WeilConjectures.AlgebraicGeometry.CompatibleImmersionGluing, whose unchanged theorem is:

```lean
theorem exists_gluedCompatibleImmersionCharts (S : Scheme.{u})
    (U : S → S.Opens)
    (W : S → Scheme.{u}) (j : ∀ s : S, W s ⟶ (U s).toScheme)
    (hj : ∀ s : S, IsImmersion (j s))
    (hcompat : ∀ (i k : S) {T : Scheme.{u}}
      (a : T ⟶ (U i).toScheme) (b : T ⟶ (U k).toScheme),
      a ≫ (U i).ι = b ≫ (U k).ι →
      ((∃ h : T ⟶ W i, h ≫ j i = a) ↔ (∃ h : T ⟶ W k, h ≫ j k = b))) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ S),
      ∀ i : S, ∃ e : W i ⟶ Z, IsPullback (j i) e (U i).ι q
```

Both private helper proofs and the complete public proof already exist upstream.
No target, statement of a node, definition, or unit route changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompatibleImmersionGluing | W3 | Withdraw the duplicate module. |
| WeilConjectures.AlgebraicGeometry.LocalImmersionLocus | unclaimed | Already imports the upstream twin and applies its current signature; no edit. |

There are no direct importers of the withdrawn Sheaf module in the current tree.
The upstream consumer above is listed to document the former use and retained route.
The DAG node lem-sc-compatible-immersion-gluing is redirected to upstream.

## Status

landed 20261020T135436-L-1824026 2026-10-20 (merge of deliver/W3/Sheaf.AlgebraicGeometry.CompatibleImmersionGluing)
