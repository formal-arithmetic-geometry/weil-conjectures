# SheafOfModules.RingedProperOpen.gamma

## Reason

The kernel times out checking an instantiation of the unit/map/counit formula after
unfolding the specialized gamma construction, even though elaboration takes under
one second. Factor its actual formula into a generic constructor and specialize
that constructor; this prevents repeated expansion of the derived localization
functors. The generic constructor has the exact former unit/whiskering/counit body.

## Old

```lean
def gamma {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) (R : Rings m T) :
    (o.operation r R).right ⋙ o.shriek i R ⟶
      o.shriek k R ⋙ (o.operation p R).right :=
  Functor.whiskerLeft ((o.operation r R).right ⋙ o.shriek i R)
      (o.operation p R).derivedAdjunction.unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (o.operation r R).right (t e k r p i d R))
      (o.operation p R).right ≫
    Functor.whiskerRight
      (Functor.whiskerRight (o.operation r R).derivedAdjunction.counit (o.shriek k R))
      (o.operation p R).right
```

## New

```lean
def gamma {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) (R : Rings m T) :
    (o.operation r R).right ⋙ o.shriek i R ⟶
      o.shriek k R ⋙ (o.operation p R).right :=
  properOpenMate (o.operation p R).derivedAdjunction
    (o.operation r R).derivedAdjunction (o.shriek i R) (o.shriek k R)
    (t e k r p i d R)
```

The new public constructor properOpenMate is explicitly defined by the former
three-factor formula at generic categories. Thus gamma has the identical
statement and is definitionally the same transformation. No target is affected
in meaning. Since the body of a public definition changes syntactically, the
independent review must verify this definitional equality, including for targets
that depend on it.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedProperOpenCoefficientSquare | M9 | gamma and its private adjunct proof use the generic constructor; left/right and the theorem retain their signatures and meaning |

No external declaration uses gamma by name; no external proof adaptation is needed.

## Status

landed 20261025T211954-L-4179387 2026-10-25 (merge of deliver/M9/Sheaf.Paper.RingedProperOpenCoefficientSquare)
