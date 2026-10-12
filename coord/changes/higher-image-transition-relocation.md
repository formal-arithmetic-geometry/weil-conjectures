# AlgebraicGeometry.Etale.lowerStarPlusTransition and higher-image transitions

## Reason

The source definitions must be available to independent coherence and affine-continuity
modules that the original Transition module imports. Keeping their declarations in that
module would create an import cycle. Expanding their formulas into parameter hypotheses
also caused kernel checking to exceed the single-file 60-second limit. Move the three
existing definitions verbatim to Sheaf.AlgebraicGeometry.HigherDirectImageTransitions,
then publicly import this module from the original source module. No notion is duplicated.

## Old

Declared in WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition:

```lean
section Transition

variable {X Y Y' : Scheme.{u}}

/-- The transition map `Rh_* K ⟶ Rh'_* (a^* K)` attached to a commutative triangle
`a ≫ h = h'`: the unit of `Lh'^* ⊣ Rh'_*` at `Rh_* K`, followed by `Rh'_*` applied to the
composition isomorphism `Lh'^* ≅ Lh^* ⋙ La^*` and to `La^*` of the counit of
`Lh^* ⊣ Rh_*` at `K`. -/
noncomputable def Etale.lowerStarPlusTransition (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X)
    (w : a ≫ h = h') (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).obj K ⟶
      R+((h')_*[ModuleCat.{u + 1} Λ]).obj (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h').unit.app _ ≫
    R+((h')_*[ModuleCat.{u + 1} Λ]).map
      ((eqToIso (by rw [← w]) ≪≫ Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom.app _ ≫
        D+((a)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).counit.app K))

/-- The transition map `R^q h_* F ⟶ R^q h'_* a^* F` of higher direct images attached to a
commutative triangle `a ≫ h = h'`: the degree-`q` homology of
`AlgebraicGeometry.Etale.lowerStarPlusTransition` at `F` placed in degree `0`, followed by the
identification `a^*(F[0]) ≅ (a^* F)[0]`. -/
noncomputable def Etale.higherDirectImageTransition (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X)
    (w : a ≫ h = h') (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.higherDirectImage Λ h q F ⟶
      Etale.higherDirectImage Λ h' q (((a)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    (Etale.lowerStarPlusTransition Λ a h h' w _ ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))

/-- The transition map of higher direct images along a morphism `φ : U ⟶ V` of schemes over
`W`, for the sheaves pulled back from a fixed sheaf `G` on `W` and the structure morphisms
composed with `k : W ⟶ S`:
`R^q (V → S)_* (G|_V) ⟶ R^q (U → S)_* (G|_U)`. It is
`AlgebraicGeometry.Etale.higherDirectImageTransition` followed by the identification
`φ^*(G|_V) ≅ G|_U`. -/
noncomputable def Etale.higherDirectImageOverMap {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V : Over W}
    (φ : U ⟶ V) :
    Etale.higherDirectImage Λ (V.hom ≫ k) q (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G) ⟶
      Etale.higherDirectImage Λ (U.hom ≫ k) q (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj G) :=
  Etale.higherDirectImageTransition Λ φ.left (V.hom ≫ k) (U.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) q _ ≫
    (DerivedCategory.Plus.homologyFunctor _ q).map (R+((U.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom (Over.w φ).symm).inv.app
          G)))

end Transition
```

## New

The same three declarations, with byte-identical parsed signatures and bodies, are in
Sheaf.AlgebraicGeometry.HigherDirectImageTransitions. The original module exports them by:

```lean
public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
```

The old public imports are public imports of the new definitions module, so their exports
are retained transitively. The target theorem signature is unchanged. This is a relocation,
not a mathematical change to any target-used definition; no target meaning changes.

## Users

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Names, types, and bodies are preserved through the public import; no adaptation is needed. |

The internal uses formerly in the original module moved together with their definitions.
The new coherence and affine-continuity modules import the new definitions module directly.
Every declaration-user found by tools/downstream.py --uses keeps the same statement and
meaning, including proofs that unfold lowerStarPlusTransition. No downstream source edit
is required; the public import supplies the identical definitions.

## Status

landed 20261012T053932-L-2635421 2026-10-12 (merge of deliver/G1/WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition)
