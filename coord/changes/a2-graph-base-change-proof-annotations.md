# AlgebraicGeometry.Etale.compactSupportGraphDerivedComparison_geometric_baseChange

## Reason

The stage-3 preflight requires a change record for the local irreducibility annotation
and proof elaboration option added to the assigned module. They keep the inverse-image,
direct-image and extension functors folded during the categorical proof. They are local
proof configuration; no definition, theorem signature or public import changes. The new
import is proof-only. The original theorem is now proved from the supporting projections.
No target meaning changes and no target statement is changed.

## Old

```lean
theorem compactSupportGraphDerivedComparison_geometric_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f) (y : X) :
    Functor.whiskerRight
        (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c))
        (upperStar (ModuleCat.{u + 1} A) (X.algClosurePoint y)).mapDerivedCategory ≫
      exactCompactSupportExchange A c (X.algClosurePoint y) =
    (exactEtaleSumExchange A f (X.algClosurePoint y)).hom ≫
      Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} A)
          (pullback.snd (X.algClosurePoint y) f)).mapDerivedCategory
        (compactSupportDerivedComparison A (pullback.fst (X.algClosurePoint y) f)
          (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)
          (etaleCompactificationGraphMap A (pullback.fst (X.algClosurePoint y) f)
            (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)))
```

The old file has no local irreducibility attribute or backward definitional-equality option.

## New

```lean
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] upperStar lowerStar etaleLowerShriek openImmersionLowerShriek

theorem compactSupportGraphDerivedComparison_geometric_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f) (y : X) :
    Functor.whiskerRight
        (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c))
        (upperStar (ModuleCat.{u + 1} A) (X.algClosurePoint y)).mapDerivedCategory ≫
      exactCompactSupportExchange A c (X.algClosurePoint y) =
    (exactEtaleSumExchange A f (X.algClosurePoint y)).hom ≫
      Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} A)
          (pullback.snd (X.algClosurePoint y) f)).mapDerivedCategory
        (compactSupportDerivedComparison A (pullback.fst (X.algClosurePoint y) f)
          (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)
          (etaleCompactificationGraphMap A (pullback.fst (X.algClosurePoint y) f)
            (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)))
```

The theorem signature is verbatim identical. The displayed commands affect elaboration
inside this module. The actual new definitions are in five newly introduced supporting
modules; they do not replace existing definitions.

## Users

`tools/downstream.py` found 225 transitive importers, but the declaration is mentioned
only by its own module and the direct consumer below. All transitive consumers keep the
same interface. No consumer source is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange | A2 | Local proof annotations and completed proof; unchanged signature. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso | unclaimed | Existing use specializes the same theorem; no adaptation. |

## Status

landed 20261018T112412-L-630984 2026-10-18 (merge of deliver/A2/Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange)
