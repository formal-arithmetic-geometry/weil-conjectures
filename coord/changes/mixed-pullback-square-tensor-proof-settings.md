# AlgebraicGeometry.mixedPullbackSquareComparison_tensor

## Reason

The completed proof adds local irreducibility attributes, local generic helpers,
and scoped omissions of the derived-category section instance from those generic
helpers. Respecting transparency prevents unnecessary unfolding of the selected
pullbacks and derived tensor structures; explicit functor-object simplification and
category/iso associativity close the required conversions. The item compiles in
about 41 seconds, within the prescribed single-file limit.

The static checker conservatively calls command changes an interface change, so this
record documents them. Every existing public signature and visibility is identical,
and the body of mixedPullbackSquareComparison is unchanged. All irreducibility
attributes are local and options affect elaboration of this file only. The generic
helpers are private and fully constructed/proved; no data is deferred. The new public
K-flat composition triangle is in its own module and has its own DAG node.

## Old

Original settings:
```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
```
Original theorem signature:
```lean
theorem mixedPullbackSquareComparison_tensor
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (P Q : schemeDerivedCategory Y) :
    (derivedPullback (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso g).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.snd f g)).hom.app
        ((derivedPullback g).obj P, (derivedPullback g).obj Q) ≫
      ((mixedPullbackSquareComparison f g).hom.app P ⊗ₘ
        (mixedPullbackSquareComparison f g).hom.app Q) =
    (mixedPullbackSquareComparison f g).hom.app (P ⊗ Q) ≫
      (derivedPullback (pullback.fst f g)).map
        ((mixedHomTensorPullbackIso f).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.fst f g)).hom.app
        ((derivedPullback f).obj P, (derivedPullback f).obj Q)
```

## New

Proof settings:
```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local irreducible] derivedPullback mixedHomTensorPullbackIso
  schemeDerivedTensorMonoidal

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```
The existing theorem signature is identical:
```lean
theorem mixedPullbackSquareComparison_tensor
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (P Q : schemeDerivedCategory Y) :
    (derivedPullback (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso g).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.snd f g)).hom.app
        ((derivedPullback g).obj P, (derivedPullback g).obj Q) ≫
      ((mixedPullbackSquareComparison f g).hom.app P ⊗ₘ
        (mixedPullbackSquareComparison f g).hom.app Q) =
    (mixedPullbackSquareComparison f g).hom.app (P ⊗ Q) ≫
      (derivedPullback (pullback.fst f g)).map
        ((mixedHomTensorPullbackIso f).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.fst f g)).hom.app
        ((derivedPullback f).obj P, (derivedPullback f).obj Q)
```
Its proof now combines K-flat naturality transport, two composition triangles,
equality transport and inverse/composite tensor compatibility. No existing public
definition or statement changes, and no adapted modules are delivered.

## Users

The downstream scan reports 338 transitive importers. The declaration-name scan
finds the item and MixedTensorPairingBaseChangeTransport as declaration users.
These users retain precisely the same statements and definitions. Local proof
attributes and settings are not exported, so no module requires adaptation and no
target statement needs a semantic rereading.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.MixedPullbackSquareTensorCoherence | H1 | Original statement and comparison definition unchanged; theorem reduced to the K-flat triangle. |
| Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChangeTransport | unclaimed | Existing theorem application remains identical; no edit needed. |

## Status

landed 20261013T172654-L-2099053 2026-10-13 (merge of deliver/H1/Sheaf.AlgebraicGeometry.MixedPullbackSquareTensorCoherence)
