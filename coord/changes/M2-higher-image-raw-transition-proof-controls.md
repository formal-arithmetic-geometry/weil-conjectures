# AlgebraicGeometry.Etale.higherDirectImageRawTransition_toHom_core

## Reason

The core proof requires local transparency controls to prevent large derived-category constructions from unfolding during instance conversion. The preflight conservatively classifies changed open/attribute/option commands as an interface change, so this record documents their scope. All existing declaration signatures and definitions remain unchanged; no target meaning changes and no statement review is reopened.

## Old

The module opened `CategoryTheory Opposite` and had no additional local irreducibility attributes. Its theorem had this signature (verbatim):

```lean
theorem higherDirectImageRawTransition_toHom_core
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale) :
    (higherDirectImagePresheafToHom Λ h' q K').app (op U) ∘
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U) =
      (higherDirectImagePresheafToHom Λ h q K).app (op U) ≫
        (Functor.whiskerLeft (freeSheaf Λ S).op (preadditiveYoneda.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map
            (lowerStarPlusTransition Λ a h h' w K ≫
              R+((h')_*[ModuleCat.{u + 1} Λ]).map v)))).app (op U)
```

The body was `by sorry`.

## New

The theorem has exactly the same signature:

```lean
theorem higherDirectImageRawTransition_toHom_core
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale) :
    (higherDirectImagePresheafToHom Λ h' q K').app (op U) ∘
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U) =
      (higherDirectImagePresheafToHom Λ h q K).app (op U) ≫
        (Functor.whiskerLeft (freeSheaf Λ S).op (preadditiveYoneda.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map
            (lowerStarPlusTransition Λ a h h' w K ≫
              R+((h')_*[ModuleCat.{u + 1} Λ]).map v)))).app (op U)
```

Its body is the derived-adjunction/homology reduction in the delivered module. New results are imported with plain proof-only imports. Private local proof helpers, including the kernel-checked congruence generator, are added.

The module also opens `CategoryTheory.Limits` for its proof helpers. The proof uses `backward.isDefEq.respectTransparency = true`, and local irreducibility attributes for upperStarPlusComp, upperStarComp, mapDerivedCategoryPlusSingleFunctor, lowerStarPlusTransition, higherDirectImagePresheafToHom, Adjunction.homEquiv, Adjunction.derivedPlus, and derivedUpperStarLowerStarAdjunctionPlus. These attributes are local to this module. The existing public theorem's signature is elaborated with the original `backward.isDefEq.respectTransparency = false`; only its proof uses the new option. No new global instance or notation is registered.

## Users

Read-only `tools/downstream.py --uses higherDirectImageRawTransition_toHom_core` found 218 downstream modules, but only HigherDirectImageRawTransitionToHom mentions this declaration. The item itself is also listed by that command. Neither mathematical interface changes, so no adaptation is required. The other 217 downstream modules import the result transitively and inherit the same signatures and definitions.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore` | M2 | Proof changes; its original signature remains byte-for-byte identical. |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom` | unclaimed (no claim lock on this clone) | Applies the same theorem at the same arguments; no statement or definition changes, no adaptation. |

The new RawTriangleAdjunct and TransitionHomologyShift modules have no existing downstream users. Their new statements have their own nodes. None of the new mathematical definitions chooses data from an unproved existence statement: there are no new mathematical data definitions at all.

## Status

landed 20261014T010846-L-3165316 2026-10-14 (merge of deliver/M2/Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore)
