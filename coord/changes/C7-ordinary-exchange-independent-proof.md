# Independent ordinary exchange and compactification exchange proofs

## Reason

The returned delivery closed an import cycle through OrdinaryBasicSquare,
IntegralOrdinaryCompactificationSquares, IntegralOrdinaryExchangeProjectionSquares,
IntegralOrdinaryExchangeSquare and IntegralOrdinaryCompactificationExchangeSquare.
The two exchange component modules are unclaimed in the current claim records.
Replace their circular applications of ordinaryBasicSquare by independent proofs;
all existing public signatures, visibility and public imports stay unchanged.

## Old

`Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare`:

```lean
theorem ordinaryExchangeSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left) :
    ∀ {U V W Z : Over B}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      (hr : IsProper r.left) (hp : IsProper p.left)
      (w : k.left ≫ p.left = r.left ≫ i.left) (e : Expression B I X V),
      (Expression.pull i (.push p hp e)).ordinaryReduction l E o a K ≫
        (properExchange l E o a.compositors k.left r.left p.left i.left w).app
          (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E W.left).reduction.map
          ((mateEquiv (ringedAdj l E p.left) (ringedAdj l E r.left)
            (TwoSquare.mk _ _ _ _
              (ringedSquare l E k.left r.left p.left i.left w).hom)).natTrans.app
                (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.push r hr (.pull k e)).ordinaryReduction l E o a K
```

`Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare`:

```lean
theorem ordinaryCompactificationExchangeSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V U' V' : Over B}
    (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
    (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
    (hi : IsPullback x.left cf'.i cf.i z) (e : Expression B I X U) :
    (Expression.pull y (.compactSupport f cf e)).ordinaryReduction l E o a K ≫
        (compactificationExchange l E o a.compositors a.openComparisons
          cf cf' x.left y.left z wi wp hi).app
            (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V'.left).reduction.map
          ((ringedCompactificationExchange l E a.ringedModels a.ringedOpenComparisons
            cf cf' x.left y.left z wi wp hi).app (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f' cf' (.pull x e)).ordinaryReduction l E o a K
```

Each old proof imports OrdinaryBasicSquare and applies it to the corresponding
BasicPair constructor, so importing the components into the parent creates a cycle.


## New

`Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare`:

```lean
theorem ordinaryExchangeSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left) :
    ∀ {U V W Z : Over B}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      (hr : IsProper r.left) (hp : IsProper p.left)
      (w : k.left ≫ p.left = r.left ≫ i.left) (e : Expression B I X V),
      (Expression.pull i (.push p hp e)).ordinaryReduction l E o a K ≫
        (properExchange l E o a.compositors k.left r.left p.left i.left w).app
          (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E W.left).reduction.map
          ((mateEquiv (ringedAdj l E p.left) (ringedAdj l E r.left)
            (TwoSquare.mk _ _ _ _
              (ringedSquare l E k.left r.left p.left i.left w).hom)).natTrans.app
                (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.push r hr (.pull k e)).ordinaryReduction l E o a K
```

`Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare`:

```lean
theorem ordinaryCompactificationExchangeSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V U' V' : Over B}
    (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
    (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
    (hi : IsPullback x.left cf'.i cf.i z) (e : Expression B I X U) :
    (Expression.pull y (.compactSupport f cf e)).ordinaryReduction l E o a K ≫
        (compactificationExchange l E o a.compositors a.openComparisons
          cf cf' x.left y.left z wi wp hi).app
            (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V'.left).reduction.map
          ((ringedCompactificationExchange l E a.ringedModels a.ringedOpenComparisons
            cf cf' x.left y.left z wi wp hi).app (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f' cf' (.pull x e)).ordinaryReduction l E o a K
```

The new proofs import no OrdinaryBasicSquare. In the compactification-exchange
module, private helpers prove mate pasting, insertion of a child coefficient,
the pullback boundary, open beta compatibility, and final compactification
pasting. Whole-transformation equalities normalize the two compactification maps;
components are taken only inside the generic categorical pasting theorem.
Its inferred proof function is applied using explicit congruence proofs following
the private method of IntegralOrdinaryProperOpenSquare. All generated proofs
are checked by the kernel; no declaration of that module is changed. ordinaryCompactificationExchangeSquare specializes the final generic
helper by exact. ordinaryExchangeSquare imports all of that module and specializes
only its private primitive mate and pullback helpers; it does not use the
compactification theorem. Local irreducibility attributes limit elaboration
without changing any global attribute or definition. No sorry is added.


## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.OrdinaryBasicSquare | C7 | Uses the independent component proofs for its BasicPair cases. |
| Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare | unclaimed | Replaces the circular parent application by a primitive mate proof. |
| Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare | unclaimed | Replaces the circular parent application by proper/open pasting. |
| Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares | unclaimed | The public component type is unchanged; recompiled without edits. |
| Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares | unclaimed | The public component type is unchanged; recompiled without edits. |

A source search finds no other callers of either public exchange theorem. No
public helper is added: import all is used to share the proved private helpers.

## Status

landed 20261028T072350-L-1937649 2026-10-28 (merge of deliver/C7/Sheaf.SixFunctors.OrdinaryBasicSquare)
