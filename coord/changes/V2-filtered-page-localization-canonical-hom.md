# CategoryTheory.finiteFilteredCohomology

## Reason

Restore the module archived at
`quarantine/Sheaf/Algebra/Homology/FilteredPageLocalization.lean` by the upstream sync.
The rework row reports unknown `FilteredObject.HomPreservingSteps.mk` in the identity
and composition laws. The current canonical category uses `FilteredObject.Hom`.
Replace only the two constructor names by `FilteredObject.Hom.mk`; the existing
`congr 1` and cohomology functor laws then prove the same equations. All object and
map constructions, signatures, visibility, imports and mathematical statements are
preserved. No target statement or definition meaning changes.

Also prove the two existing auxiliary theorem holes by cokernel projection/descent
and the image-of-composite inclusion. These are proof changes, not interface changes.

## Old

```lean
noncomputable def finiteFilteredCohomology (R : Type u) [CommRing R] (n : ℤ) :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ FilteredObject (ModuleCat.{u} R) where
  obj U := ⟨U.obj.obj.homology n, finiteFilteredCohomologyFiltration R U n⟩
  map {U V} f :=
    { hom := HomologicalComplex.homologyMap f.hom.hom n
      preserves := fun a ↦ by
        let sq : Arrow.mk (HomologicalComplex.homologyMap
            (U.obj.filtration.step a).arrow n) ⟶
            Arrow.mk (HomologicalComplex.homologyMap (V.obj.filtration.step a).arrow n) :=
          Arrow.homMk (HomologicalComplex.homologyMap
            (FilteredObject.restrictionSteps f.hom a) n)
            (HomologicalComplex.homologyMap f.hom.hom n) (by
              dsimp only [Arrow.mk_hom]
              rw [← HomologicalComplex.homologyMap_comp,
                ← HomologicalComplex.homologyMap_comp]
              congr 1
              exact Classical.choose_spec (f.hom.preserves a))
        exact ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩ }
  map_id U := by
    change FilteredObject.HomPreservingSteps.mk _ _ =
      FilteredObject.HomPreservingSteps.mk _ _
    congr 1
    exact HomologicalComplex.homologyMap_id U.obj.obj n
  map_comp f g := by
    change FilteredObject.HomPreservingSteps.mk _ _ =
      FilteredObject.HomPreservingSteps.mk _ _
    congr 1
    exact HomologicalComplex.homologyMap_comp f.hom.hom g.hom.hom n
```

## New

```lean
noncomputable def finiteFilteredCohomology (R : Type u) [CommRing R] (n : ℤ) :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ FilteredObject (ModuleCat.{u} R) where
  obj U := ⟨U.obj.obj.homology n, finiteFilteredCohomologyFiltration R U n⟩
  map {U V} f :=
    { hom := HomologicalComplex.homologyMap f.hom.hom n
      preserves := fun a ↦ by
        let sq : Arrow.mk (HomologicalComplex.homologyMap
            (U.obj.filtration.step a).arrow n) ⟶
            Arrow.mk (HomologicalComplex.homologyMap (V.obj.filtration.step a).arrow n) :=
          Arrow.homMk (HomologicalComplex.homologyMap
            (FilteredObject.restrictionSteps f.hom a) n)
            (HomologicalComplex.homologyMap f.hom.hom n) (by
              dsimp only [Arrow.mk_hom]
              rw [← HomologicalComplex.homologyMap_comp,
                ← HomologicalComplex.homologyMap_comp]
              congr 1
              exact Classical.choose_spec (f.hom.preserves a))
        exact ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩ }
  map_id U := by
    change FilteredObject.Hom.mk _ _ = FilteredObject.Hom.mk _ _
    congr 1
    exact HomologicalComplex.homologyMap_id U.obj.obj n
  map_comp f g := by
    change FilteredObject.Hom.mk _ _ = FilteredObject.Hom.mk _ _
    congr 1
    exact HomologicalComplex.homologyMap_comp f.hom.hom g.hom.hom n
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FilteredPageLocalization | V2 | Restore the full quarantined source and repair its two functor-law proofs; all 28 declarations retained. |
| Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence | quarantined; separate item | Its proof import is preserved. The restored module has the same public signatures and constructions, so no consumer edit is needed. |

The live-tree `tools/downstream.py` reports the item as unknown because it is quarantined.
A source search over both `lean/` roots and `quarantine/` found the consumer above.
The DAG parent is `lem-kun-bounded-tensor-tor-spectral-sequence`; its dependency is retained.
No consumer is weakened, repointed or withdrawn. No other module is adapted.

## Status

landed 20261020T174911-L-818105 2026-10-20 (merge of deliver/V2/Sheaf.Algebra.Homology.FilteredPageLocalization)
