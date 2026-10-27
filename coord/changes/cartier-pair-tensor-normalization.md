# cartierPairTensorFrames

## Reason

Normalize the tensor-frame map using the monoidal comparison on the pulled-back unit. The old expression repeatedly converted the ordinary unit into two pulled-back units, causing expensive definition reductions in coherence proofs. The proved `tensorPullbackFrames_eq_unit` theorem, using monoidal left unitality, proves the expressions equal; the normalization preserves the constructed morphism and all target meanings. The base morphism is written using the site functor stored by the frame torsor; it is definitionally equal to `U.hom`, and prevents repeated reductions between the two presentations.

## Old

```lean
def cartierPairTensorFrames {T : Scheme.{u}} (L M : T.Modules) (U : T.Etale)
    (x : (Scheme.Modules.pullback U.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.hom).obj L)
    (y : (Scheme.Modules.pullback U.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.hom).obj M) :
    (Scheme.Modules.pullback U.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.hom).obj (L ⊗ M) :=
  (Scheme.Modules.pullbackObjUnitIso U.hom).hom ≫
    (λ_ (Scheme.Modules.unit U.left)).inv ≫
    ((Scheme.Modules.pullbackObjUnitIso U.hom).inv ⊗ₘ
      (Scheme.Modules.pullbackObjUnitIso U.hom).inv) ≫
    (x ⊗ₘ y) ≫ (Functor.Monoidal.μIso (Scheme.Modules.pullback U.hom) L M).hom
```

## New

```lean
def cartierPairTensorFrames {T : Scheme.{u}} (L M : T.Modules) (U : T.Etale)
    (x : (Scheme.Modules.pullback U.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.hom).obj L)
    (y : (Scheme.Modules.pullback U.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.hom).obj M) :
    (Scheme.Modules.pullback U.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.hom).obj (L ⊗ M) :=
  Scheme.Modules.tensorPullbackFrames L M
    ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).obj U).hom x y
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartierPairTensorAddition | G2 | Its tensor compatibility proofs use the normalized expression. |

`tools/downstream.py Sheaf.AlgebraicGeometry.CartierPairTensorAddition --uses cartierPairTensorFrames` reports only this module and no downstream modules. No signature, hypothesis, conclusion or constructed map changes.

## Status

landed 20261025T003320-L-3227535 2026-10-25 (merge of deliver/G2/Sheaf.AlgebraicGeometry.CartierPairTensorAddition)
