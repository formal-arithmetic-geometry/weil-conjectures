# AlgebraicGeometry.Scheme.picard_termwise_source_coherence

## Reason

Restore the module preserved in quarantine by the cluster restore recorded in
coord/rework.tsv. Its absence does not withdraw the mathematical obligation: the
quarantined PicardTermwiseModelComparison module imports it and applies its theorem.
The existing DAG attachment and all dependencies are retained. The proof constructs
its comparison family from the explicit canonical single maps. No object is chosen
from a mere existence theorem. Mathlib's Iso.eq_inv_comp expresses the final
cancellation directly.

No public signature, definition, import, target meaning, or unit route changes.
No adopted-source module is edited and no consumer adaptation is necessary.

## Old

There is no file at the live lean/ path. The quarantined declaration has this signature:

```lean
theorem picard_termwise_source_coherence (W : Scheme.{v}) :
    ∃ a : ∀ {T : Scheme.{v}} (t : T ⟶ W),
        (derivedPullback t).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
          DerivedCategory.Q.obj (picardTermwiseSource t),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (ht : i ≫ t = t'),
      let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
          eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
      (a t').hom ≫ DerivedCategory.Q.map (picardTermwiseSourceRestrictionIso i t t' ht).hom =
        c.inv.app _ ≫ (derivedPullback i).map (a t).hom ≫
          (picardTermwiseCounit i).app (picardTermwiseSource t)
```

The archived proof finishes by applying congrArg to precompose with c.inv, then
simplifying associativity and the inverse-hom identity.

## New

The restored declaration has the identical signature:

```lean
theorem picard_termwise_source_coherence (W : Scheme.{v}) :
    ∃ a : ∀ {T : Scheme.{v}} (t : T ⟶ W),
        (derivedPullback t).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
          DerivedCategory.Q.obj (picardTermwiseSource t),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (ht : i ≫ t = t'),
      let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
          eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
      (a t').hom ≫ DerivedCategory.Q.map (picardTermwiseSourceRestrictionIso i t t' ht).hom =
        c.inv.app _ ≫ (derivedPullback i).map (a t).hom ≫
          (picardTermwiseCounit i).app (picardTermwiseSource t)
```

The final step is `(c.app _).eq_inv_comp.mpr h`, using the existing single-map
composition equation. The rest of the construction and the imports are preserved.

## Users

The downstream.py command reports the live module as unknown because it is
quarantined. Searches of lean/ and quarantine/ find the direct consumer below.
A scan of all DAG stmt_deps, proof_deps, and proof-step uses finds the same parent.
The current unit realization does not require a different route.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardTermwiseSourceCoherence | M4 | Restore the complete theorem. |
| Sheaf.AlgebraicGeometry.PicardTermwiseModelComparison | unclaimed | Same theorem and comparison coherence; no adaptation. |

## Status

landed 20261021T002145-L-1492935 2026-10-21 (merge of deliver/M4/Sheaf.AlgebraicGeometry.PicardTermwiseSourceCoherence)
