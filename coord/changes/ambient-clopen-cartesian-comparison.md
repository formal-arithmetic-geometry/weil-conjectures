# AlgebraicGeometry.ProEtale.AmbientClopenRestriction.cartesianPull

## Reason

Repeated conversion of the compositor/equality-isomorphism expression through the Option
coefficient dispatcher exceeds the kernel-checking limit. Dispatch directly to the published
strict/varying `moduleSquareG` for the same Cartesian square, in the inverse orientation.
Their `moduleSquareG_eq` theorems specify exactly the original compositor formula: invert
the three factors and use the symmetry of the pullback condition. No statement or target
signature changes; targets using this definition should be reread with this API refactoring.

## Old

```lean
def cartesianPull (m : Option ℕ) {V W Z : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z) :
    pull l E m i ⋙ pull l E m (pullback.snd p i) ≅
      pull l E m p ⋙ pull l E m (pullback.fst p i) :=
  (pullComp l E m (pullback.snd p i) i).symm ≪≫
    eqToIso (congrArg (pull l E m) (pullback.condition (f := p) (g := i)).symm) ≪≫
    pullComp l E m (pullback.fst p i) p
```

## New

```lean
def cartesianPull (m : Option ℕ) {V W Z : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z) :
    pull l E m i ⋙ pull l E m (pullback.snd p i) ≅
      pull l E m p ⋙ pull l E m (pullback.fst p i) :=
  match m with
  | some n => (StrictTower.moduleSquareG (scalarRings l E n)
      (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm).symm
  | none => (VaryingRing.moduleSquareG (scalarRings l E) (scalarTransitions l E)
      (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm).symm
```

The existing comparison is uniquely specified by its equality theorem; no arbitrary
existence witness is introduced. The inverse open-unit normalization now uses that exact
comparison instead of comparing an expanded copy with it.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | R2 | same canonical square comparison |

`tools/downstream.py ... --uses cartesianPull` reports only this item and zero downstream
modules in the current source. No forced adaptations.

## Status

landed 20261025T181016-L-4062981 2026-10-25 (merge of deliver/R2/Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness)
