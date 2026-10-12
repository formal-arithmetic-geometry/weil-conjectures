# AlgebraicGeometry.Etale.etaleSetPullback_eq_sheafEquivalence

## Reason

Uniqueness of left adjoints supplies a natural isomorphism, not functor equality.
The reviewer requested this correction of the new intermediate statement.

## Old

```lean
 theorem etaleSetPullback_eq_sheafEquivalence {X X' : Scheme.{u}} (u : X' ⟶ X)
    [IsUniversalHomeomorphism u] :
    (sheafEquivalence (Type (u + 1)) u).symm.functor = Scheme.etaleSetPullback u
```

## New

```lean
 theorem etaleSetPullback_eq_sheafEquivalence {X X' : Scheme.{u}} (u : X' ⟶ X)
    [IsUniversalHomeomorphism u] :
    Nonempty ((sheafEquivalence (Type (u + 1)) u).symm.functor ≅
      Scheme.etaleSetPullback u)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance | C1 | Change the inverse equivalence's functor along the comparison isomorphism; parent signature preserved. |

The comparison is a new module of this delivery; the repository has no other
users of its declaration. The three supporting nodes may use this comparison
in their documented arguments, without changing their statements.

## Status

landed 20261012T070531-L-3468192 2026-10-12 (merge of deliver/C1/Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance)
