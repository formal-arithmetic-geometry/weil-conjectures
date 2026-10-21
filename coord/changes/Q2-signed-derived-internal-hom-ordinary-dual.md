# CategoryTheory.RingedHomUniverses.ordinaryDual

## Reason

Expose the object and morphism fields of the private ordinary-Hom functor directly.
The equivalent uncurried-product presentation inserts an identity map on the fixed
second variable into every map. Repeated comparison of those expressions while
converting shift conventions makes the concrete proof expensive to elaborate.
The explicit functor uses exactly the same Hom complex and contravariant map;
the functor laws are proved from those of homComplexFunctor. There is no public
signature or mathematical definition change.

## Old

```lean
private def ordinaryDual (I : Complex.{c, v, r} J R) :
    OppositeShift (Complex.{c, v, r} J R) ℤ ⥤
      PullbackShift (Complex.{c, v, r} J R) negInt :=
  Prod.sectL _ I ⋙ ordinaryBifunctor.{c, v, r} J R
```

## New

```lean
private def ordinaryDual (I : Complex.{c, v, r} J R) :
    OppositeShift (Complex.{c, v, r} J R) ℤ ⥤
      PullbackShift (Complex.{c, v, r} J R) negInt where
  obj E := complexHom.{c, v, r} J R E.unop I
  map f := (homComplexFunctor.{c, v, max c v r, max c v r} (R := R).map f).app I
  map_id E := by
    simp only [Functor.map_id, NatTrans.id_app]
    rfl
  map_comp f g := by simp only [Functor.map_comp, NatTrans.comp_app]
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SignedDerivedInternalHomExact | Q2 | Adapt private naturality proof to the direct map; all new cone and descent helpers use it. |

The declaration is private; no other module imports it with `import all` or
mentions it. The public consumer CoefficientBidualTriangleCompatibility uses
only signedDerivedInternalHom_exact, whose signature and visibility are unchanged.

## Status

landed 20261021T061633-L-1803618 2026-10-21 (merge of deliver/Q2/Sheaf.CategoryTheory.SignedDerivedInternalHomExact)
