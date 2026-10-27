# SheafOfModules.RingedProperOpen.left

## Reason

Kernel profiling shows that the derived-category specialization stalls while comparing
expanded whiskering and composition definitions. Factor the exact generic formula into
`properOpenLeft` before specializing, so the completed generic identity applies
to identical constructor applications. The unit, coefficient mate and counit maps and their
composition order are unchanged.

## Old

```lean
def left {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) {A B : Rings m T} (a : A ⟶ B) :
    (o.operation r A).right ⋙ o.shriek i A ⋙ (o.scalar Z a).T ⟶
      (o.scalar U a).T ⋙ o.shriek k B ⋙ (o.operation p B).right :=
  Functor.whiskerRight (gamma e k r p i d A) (o.scalar Z a).T ≫
    Functor.whiskerLeft (o.shriek k A) (sc.chi p a) ≫
    Functor.whiskerRight (sc.delta k a).hom (o.operation p B).right
```

## New

```lean
def left {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) {A B : Rings m T} (a : A ⟶ B) :
    (o.operation r A).right ⋙ o.shriek i A ⋙ (o.scalar Z a).T ⟶
      (o.scalar U a).T ⋙ o.shriek k B ⋙ (o.operation p B).right :=
  properOpenLeft
    (UA := category c U A) (VA := category c V A)
    (WA := category c W A) (ZA := category c Z A)
    (UB := category c U B) (VB := category c V B)
    (WB := category c W B) (ZB := category c Z B)
    (lpA := (o.operation p A).left) (rpA := (o.operation p A).right)
    (lpB := (o.operation p B).left) (rpB := (o.operation p B).right)
    (lrA := (o.operation r A).left) (rrA := (o.operation r A).right)
    (lrB := (o.operation r B).left) (rrB := (o.operation r B).right)
    (su := (o.scalar U a).T) (sv := (o.scalar V a).T)
    (sw := (o.scalar W a).T) (sz := (o.scalar Z a).T)
    (iA := o.shriek i A) (iB := o.shriek i B)
    (kA := o.shriek k A) (kB := o.shriek k B)
    (o.operation p A).derivedAdjunction (o.operation p B).derivedAdjunction
    (o.operation r A).derivedAdjunction (o.operation r B).derivedAdjunction
    (sc.pull p a).hom (sc.pull r a).hom (sc.delta i a).hom (sc.delta k a).hom
    (t e k r p i d A) (t e k r p i d B)
```

Unfolding the generic constructor, `properOpenMate`, `gamma`, and
`ScalarComparisons.chi` gives the former definition verbatim. This syntactic body change
requires independent verification of definitional equality for dependent targets.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedProperOpenCoefficientSquare | M9 | the private square proof uses the generic constructor; the statement and maps are preserved |

`tools/downstream.py --uses` finds no external consumer of this declaration.

## Status

landed 20261025T211954-L-4179387 2026-10-25 (merge of deliver/M9/Sheaf.Paper.RingedProperOpenCoefficientSquare)
