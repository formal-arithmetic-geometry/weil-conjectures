# standardSingleBaseChange_topRestriction_compatibility

## Reason

The old statement quantified over every source isomorphism `e`.  The dual-number
counterexample in return X-790d9 shows this is false: composing the canonical
comparison with a source swap changes the kernel of the base-change map.  The
parent theorem uses the canonical constructed comparison, so the interface is
repaired by requiring `e = standardSingleBaseChange_topRestriction_sourceIso p M`.

## Old

```lean
theorem standardSingleBaseChange_topRestriction_compatibility
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    ∀ (e : (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage ((⊤ : Y.Opens).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (M.restrict (⊤ : Y.Opens).ι))),
      ∃ (t : (schemeDerivedDirectImage
          (pullback.snd ((⊤ : Y.Opens).ι ≫ p) g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj
              (pullback.fst ((⊤ : Y.Opens).ι ≫ p) g)
              (M.restrict (⊤ : Y.Opens).ι))) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          standardSingleBaseChangeMap ((⊤ : Y.Opens).ι ≫ p)
            (M.restrict (⊤ : Y.Opens).ι) g ≫ t.hom
```

## New

```lean
theorem standardSingleBaseChange_topRestriction_compatibility
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    ∀ (e : (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage ((⊤ : Y.Opens).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (M.restrict (⊤ : Y.Opens).ι))),
      e = standardSingleBaseChange_topRestriction_sourceIso p M → ∃ (t : (schemeDerivedDirectImage
          (pullback.snd ((⊤ : Y.Opens).ι ≫ p) g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj
              (pullback.fst ((⊤ : Y.Opens).ι ≫ p) g)
              (M.restrict (⊤ : Y.Opens).ι))) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          standardSingleBaseChangeMap ((⊤ : Y.Opens).ι ≫ p)
            (M.restrict (⊤ : Y.Opens).ι) g ≫ t.hom
```

The full verbatim Lean statement is recorded in the compatibility node and its
`lean.statement` field.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction | unclaimed | Forced proof adaptation: construct `let e := standardSingleBaseChange_topRestriction_sourceIso p M` and pass `rfl` to the repaired compatibility theorem; parent theorem signature is unchanged. |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux | G1 | The compatibility declaration and its node statement are repaired; canonical source definition is added. |

## Status

landed 20261014T022543-L-4044816 2026-10-14 (merge of deliver/G1/Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux)
