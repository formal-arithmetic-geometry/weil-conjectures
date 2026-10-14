# Open injective coefficient lower comparison factorization

## Reason

Repair reviewer X-f2fe0 point 6. The factorization theorem has no
`BaseChangeProperty` hypothesis, and its mate computation does not use the
`BaseChangeProperty` node. Remove that unused node from the factorization
node's statement and proof dependency metadata. The Lean theorem signature is
unchanged.

## Old

The factorization theorem signature was:

```lean
theorem open_injective_coefficient_lower_comparison_factorization
    (Λ : Type (u + 1)) [CommRing Λ]
    {Y T V W : Scheme.{u}}
    (e : Y ⟶ T) (j : V ⟶ T) (eV : W ⟶ V) (a : W ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (wa : a ≫ e = eV ≫ j) (sq : IsPullback eV a j e)
    (n : ℤ) (J : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus.unit.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
              (((j)_*[ModuleCat.{u + 1} Λ]).obj J))) ≫
        R+((a)_*[ModuleCat.{u + 1} Λ]).map
          ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
            eqToHom (by rw [wa]) ≫
            (upperStarPlusComp (ModuleCat.{u + 1} Λ) eV j).hom.app _ ≫
            D+((eV)^*[ModuleCat.{u + 1} Λ]).map
              ((((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
                (((j)_*[ModuleCat.{u + 1} Λ]).obj J) ≫
                (DerivedCategory.Plus.singleFunctor _ 0).map
                  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J))))) =
      (DerivedCategory.Plus.homologyFunctor _ n).map
        (D+((e)^*[ModuleCat.{u + 1} Λ]).map
            (CategoryTheory.Functor.rightDerivedPlusSingleUnit
              ((j)_*[ModuleCat.{u + 1} Λ]) J) ≫
          (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj J))
```

Its node metadata unnecessarily included `sbc-def-base-change-property` in
`stmt_deps`, in the proof step's `uses`, and in `proof_deps`.

## New

The factorization theorem signature remains verbatim:

```lean
theorem open_injective_coefficient_lower_comparison_factorization
    (Λ : Type (u + 1)) [CommRing Λ]
    {Y T V W : Scheme.{u}}
    (e : Y ⟶ T) (j : V ⟶ T) (eV : W ⟶ V) (a : W ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (wa : a ≫ e = eV ≫ j) (sq : IsPullback eV a j e)
    (n : ℤ) (J : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus.unit.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
              (((j)_*[ModuleCat.{u + 1} Λ]).obj J))) ≫
        R+((a)_*[ModuleCat.{u + 1} Λ]).map
          ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
            eqToHom (by rw [wa]) ≫
            (upperStarPlusComp (ModuleCat.{u + 1} Λ) eV j).hom.app _ ≫
            D+((eV)^*[ModuleCat.{u + 1} Λ]).map
              ((((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
                (((j)_*[ModuleCat.{u + 1} Λ]).obj J) ≫
                (DerivedCategory.Plus.singleFunctor _ 0).map
                  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J))))) =
      (DerivedCategory.Plus.homologyFunctor _ n).map
        (D+((e)^*[ModuleCat.{u + 1} Λ]).map
            (CategoryTheory.Functor.rightDerivedPlusSingleUnit
              ((j)_*[ModuleCat.{u + 1} Λ]) J) ≫
          (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj J))
```

The node metadata now records only the declarations used by the mate
calculation:

```json
"stmt_deps": [
  "def-weil-pbc-scheme-conventions",
  "def-weil-pbc-etale-sheaves",
  "lem-weil-pbc-inverse-image-composition"
],
"proof": [
  {
    "text": "Expand the derived base-change mate and the canonical single-complex comparison; naturality of the derived unit and the adjunction triangle identities identify the composite with the displayed map.",
    "uses": [],
    "elementary": false
  }
],
"proof_deps": []
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparison` | J2 | Its proof imports and applies the factorization theorem; its theorem signature is unchanged. |

## Status

landed 20261014T174623-L-3170531 2026-10-14 (merge of deliver/J2/Sheaf.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparison)
