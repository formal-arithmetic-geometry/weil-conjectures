# finiteGeometricPurityMate and its fixed-coordinate support API

## Reason

The remaining finiteGeometricPurityMate hole needs two independent geometric
identities: base change of the inverse diagonal orientation, and base change of
the tensor counit transpose. Each needs the existing normalized source and counit
mate. Extract the existing support API so the two statements can use it without
an import cycle through the theorem they are to prove.

## Old

Sheaf.Paper.FiniteGeometricPurityMate defines the 35 existing public support
declarations from geometricPurityPullbackCommShift through geometricPurityMate,
then states finiteGeometricPurityMate with one sorry. Its original public imports
provide the geometric Frobenius, root charts, coefficient twists, exceptional
adjunction and compact-support exchange interfaces.

The three helpers had these signatures (verbatim):

```lean
private theorem geometricPurityOrigin (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
      ((Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor.obj M)) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) T M

private theorem geometricPurityPullbackOrigin (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) Y M) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X
      ((P.smoothPurityPullback g).obj M)

private theorem geometricPurityBIsIsoOfOrigin (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (gX : X ⟶ X) (gY : Y ⟶ Y) (sq : IsPullback gX f f gY)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) X M) :
    IsIso (P.geometricPurityB f aY gX gY sq M)
```

## New

The support declarations move to Sheaf.Paper.FiniteGeometricPurityCoordinates.
Their existing public signatures, definition bodies and instances are unchanged.
The retagging theorem now applies four proved private lemmas expressing the
independence of these constructions from structural-map proof data, avoiding
large specialized definitional-equality checks. All other support proofs are unchanged. Blueprint docstrings now identify their extracted coordinate node.
The three previously private, completely proved helpers geometricPurityOrigin,
geometricPurityPullbackOrigin and geometricPurityBIsIsoOfOrigin are public so the
assembly can use exactly those existing origin proofs. No existing public
visibility is reduced. Their proofs are unchanged.

The original module publicly reexports that coordinate module:

```lean
public import Sheaf.Paper.FiniteGeometricPurityCoordinates
```

All original public imports remain publicly available through that reexport.
FiniteGeometricPurityFactors introduces concrete orientation/tensor factors,
a tensor-source square, and the ordinary unit-component dualizing exchange.
Its proved geometricPurityMap_factors identifies their composite with the
existing map using existsUnique_smoothPurityTensorMap's presentation equation.
The original theorem combines the independent orientation and tensor exchange
statements and cancels the existing pulled-back purity isomorphism. Its full
signature is unchanged. No existing shared or source-library module is edited.

Their new signatures are the same, with `private` removed:

```lean
theorem geometricPurityOrigin (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
      ((Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor.obj M)) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) T M

theorem geometricPurityPullbackOrigin (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) Y M) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X
      ((P.smoothPurityPullback g).obj M)

theorem geometricPurityBIsIsoOfOrigin (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (gX : X ⟶ X) (gY : Y ⟶ Y) (sq : IsPullback gX f f gY)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) X M) :
    IsIso (P.geometricPurityB f aY gX gY sq M)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteGeometricPurityMate | P3 | Same public interface through reexport; remaining hole decomposed into two proper factor identities. |
| Sheaf.Paper.FiniteGeometricPurityCoordinates | new, P3 | Existing support API, with three proved origin helpers newly exposed. |
| Sheaf.Paper.FiniteGeometricPurityFactors | new, P3 | Concrete factor API and proved factorization. |
| Sheaf.Paper.FiniteGeometricOrientationExchange | new, P3 | Orientation-only obligation, no tensor transpose. |
| Sheaf.Paper.FiniteGeometricTensorExchange | new, P3 | Tensor-transpose obligation, no orientation, shift, roots or dimension. |

`tools/downstream.py Sheaf.Paper.FiniteGeometricPurityMate` reports zero current
Lean downstream modules. A direct-import search of lean/ and quarantine/Sheaf/
also finds none. The DAG parent thm-pur-weil-equivariance-of-purity-and-trace still
needs the original theorem. It remains attached and is not withdrawn. No
consumer adaptation is required, and none is made.

## Status

landed 20261026T200200-L-3295475 2026-10-26 (merge of deliver/P3/Sheaf.Paper.FiniteGeometricPurityMate)
