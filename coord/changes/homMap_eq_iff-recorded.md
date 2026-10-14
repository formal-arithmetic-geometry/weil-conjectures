# AlgebraicGeometry.homMap_eq_iff

## Reason

The private proof helper must compare with recordedPerfectHomMap after the
public comparison uses the original-counit lift. Its comparison-equation
side and all hypotheses stay identical; only its private conjugated-map
side changes. This follows the comparison repair in
perfectDescentComparison-original-counit.md.

## Old

```lean
private theorem homMap_eq_iff
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T)
    {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q)
    (φ : (derivedPullback (pullback.fst s T'.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T'.hom)).obj Q) :
    (perfectDescentComparison s g).hom.app P ≫
      (derivedPullback (baseChangeMap s g)).map f =
        φ ≫ (perfectDescentComparison s g).hom.app Q ↔ perfectHomMap s g f = φ
```

## New

```lean
private theorem homMap_eq_iff
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T)
    {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q)
    (φ : (derivedPullback (pullback.fst s T'.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T'.hom)).obj Q) :
    (perfectDescentComparison s g).hom.app P ≫
      (derivedPullback (baseChangeMap s g)).map f =
        φ ≫ (perfectDescentComparison s g).hom.app Q ↔ recordedPerfectHomMap s g f = φ
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | V2 | The two lifting branches use the recorded map; public theorem signature unchanged. |

This declaration is private. It has no users in any other module and is
not used by a target statement.

## Status

landed 20261014T080233-L-3750342 2026-10-14 (merge of deliver/V2/Sheaf.AlgebraicGeometry.PerfectDescendMorphisms)
