# AlgebraicGeometry.topBaseChangeAdjoint

## Reason

The consumer exceeded the 60-second compile limit (67 seconds, no Lean errors)
against this packet. Profiling the same consumer reported 51.4 seconds in type
checking, including 9.1 seconds in the comparison equality. Use the existing named
total/classical comparison in the definition, so its equality API needs no delta
reduction of the full derived construction. The module is unclaimed in the local
claim records. No statement, visibility or mathematical map changes.

## Old

In topBaseChangeAdjoint the source comparison is

```lean
  (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F q).inv
```

and the target comparison is

```lean
    (pushforward g).map (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (RingedSpace.moduleDirectImage (pullback.fst g f).toLRSHom.toShHom)
      ((tensorPullback (pullback.snd g f)).obj F) q).hom
```

The private topBaseChangeAdjoint_eq proof was

```lean
  delta schemeSingleCohomologyComparison
  rfl
```

## New

The two expressions are respectively

```lean
  (schemeSingleCohomologyComparison f F q).inv
```

and

```lean
    (pushforward g).map (schemeSingleCohomologyComparison (pullback.fst g f)
      ((tensorPullback (pullback.snd g f)).obj F) q).hom
```

The model module is publicly imported because the public definition now mentions
the named comparison. The private equality proof is `by rfl`. The wrapper's body is exactly the old
expression, so the new definition is definitionally equal to the old one.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TopBaseChangePresheaf | unclaimed | Uses the named comparison in its adjoint definition; private equality is reflexive. |
| Sheaf.AlgebraicGeometry.TopDegreeBaseChange | unclaimed | Same adjoint map and signature; no adaptation. |

## Status

landed 20261025T202016-L-2663496 2026-10-25 (merge of deliver/F9/Sheaf.AlgebraicGeometry.DerivedSquareLocalClasses)
