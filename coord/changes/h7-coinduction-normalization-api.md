# ModuleCat.bimoduleCoinductionHomIso and ModuleCat.bimoduleScalarUnit

## Reason

The normalization theorem needed to unfold both maps inside a long derived-category
equation. Repeated `change`, `simpa`, direct application and pinned-parameter versions
hit the 60-second server limit. A diagnostic compile with a lower heartbeat threshold
located the conversion at the normalization theorem application. Factor each construction
into a canonical named definition in the new coinduction-only module and retain the
existing names as abbreviations with exactly the same signatures. This leaves the actual
maps definitionally equal to their previous bodies. It introduces no new data choice:
the enriched comparison is still selected from its unique prescribed model characterization.

## Old

```lean
def bimoduleCoinductionHomIso (f : S →+* B) :
    coinductionHomLeft f ≅ coinductionHomRight f :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (algebraicShriek_derivedHom_adjunction f)))))
```

```lean
def bimoduleScalarUnit (f : S →+* B) :
    𝟙_ (DerivedCategory (ModuleCat.{u} S)) ⟶
      (restrictScalars f).mapDerivedCategory.obj (𝟙_ (DerivedCategory (ModuleCat.{u} B))) :=
  (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} S)).inv ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).map
      (ModuleCat.ofHom (Y := (restrictScalars f).obj (ModuleCat.of B B))
        { toFun := f
          map_add' := f.map_add
          map_smul' := fun s t ↦ f.map_mul s t }) ≫
    ((restrictScalars f).mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of B B) ≫
    (restrictScalars f).mapDerivedCategory.map
      (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} B)).hom
```

## New

```lean
abbrev bimoduleCoinductionHomIso (f : S →+* B) :
    coinductionHomLeft f ≅ coinductionHomRight f :=
  coinductionEnrichedHomIso f
```

```lean
abbrev bimoduleScalarUnit (f : S →+* B) :
    𝟙_ (DerivedCategory (ModuleCat.{u} S)) ⟶
      (restrictScalars f).mapDerivedCategory.obj (𝟙_ (DerivedCategory (ModuleCat.{u} B))) :=
  coinductionScalarUnit f
```

The new `ModuleCat.coinductionEnrichedHomIso` and `ModuleCat.coinductionScalarUnit`
copy the respective old expressions verbatim. The item publicly imports their module
because its definitions now refer to these canonical constructions. Every old public
signature and every other definition body remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedBimoduleTensorHom | H7 | Existing definitions become definitionally equal aliases; theorem proof completed from named lemmas. |
| Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison | unchanged; no adaptation | Only downstream importer reported by tools/downstream.py; no textual use of either repaired name, no signature or proof edit needed. |

Both `--uses` searches report only the defining item itself. No target statement or
mathematical definition changes meaning. No module held by another group is adapted.

## Status

landed 20261024T015002-L-2308078 2026-10-24 (merge of deliver/H7/Sheaf.Algebra.Homology.DerivedBimoduleTensorHom)
