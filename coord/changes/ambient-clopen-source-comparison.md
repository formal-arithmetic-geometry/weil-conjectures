# AlgebraicGeometry.ProEtale.AmbientClopenRestriction.restrictionSource

## Reason

The restriction Hom calculation needs the natural isomorphism from the k-restriction to
the composite b- and s-restrictions. Expanding the old component formula and a separately
constructed comparison caused repeated kernel conversion through chosen inverse images.
Name the existing composite isomorphism and use its inverse component in the source.
This is the same composite, with no hypothesis or conclusion change. No target signature
changes. Targets using this definition should be read with this definitional refactoring.

## Old

```lean
def restrictionSource (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (F : Modules l E m (pullback p i)) :
    (pull l E m (StrictTower.squareLift k r p i h)).obj F ⟶
      (pull l E m k).obj ((extension l E m (pullback.fst p i)).obj F) :=
  (pull l E m (StrictTower.squareLift k r p i h)).map
      ((openAdj l E m (pullback.fst p i)).unit.app F) ≫
    (pullComp l E m (StrictTower.squareLift k r p i h) (pullback.fst p i)).inv.app
      ((extension l E m (pullback.fst p i)).obj F) ≫
    (eqToIso (congrArg (pull l E m) (pullback.lift_fst k r h))).hom.app
      ((extension l E m (pullback.fst p i)).obj F)
```

## New

```lean
/-- The inverse-image comparison used by restrictionSource.
Source: Stacks 07A7 (blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def restrictionPull (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    pull l E m k ≅ pull l E m (pullback.fst p i) ⋙
      pull l E m (StrictTower.squareLift k r p i h) :=
  ((pullComp l E m (StrictTower.squareLift k r p i h) (pullback.fst p i)).symm ≪≫
    eqToIso (congrArg (pull l E m) (pullback.lift_fst k r h))).symm

def restrictionSource (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (F : Modules l E m (pullback p i)) :
    (pull l E m (StrictTower.squareLift k r p i h)).obj F ⟶
      (pull l E m k).obj ((extension l E m (pullback.fst p i)).obj F) :=
  (pull l E m (StrictTower.squareLift k r p i h)).map
      ((openAdj l E m (pullback.fst p i)).unit.app F) ≫
    (restrictionPull l E m k r p i h).inv.app
      ((extension l E m (pullback.fst p i)).obj F)
```

The new comparison is constructed, not chosen from an existence theorem. Its inverse is
the original inverse compositor followed by the same equality isomorphism.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | R2 | same source map, named comparator |

`tools/downstream.py ... --uses restrictionSource` reports only the item itself and zero
downstream modules in the current source. No forced adaptations.

## Status

landed 20261025T181016-L-4062981 2026-10-25 (merge of deliver/R2/Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness)
