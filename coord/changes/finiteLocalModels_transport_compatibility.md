# finiteLocalModels_transport_compatibility

## Reason

The old theorem asserts its law for every transport function. The docstring and
parent theorem require the transport induced by the representing isomorphism.
For compatibility, take T = U = Spec k, Q the disjoint union of two copies of U,
and E the sheaf represented by Q. Composing every point with the nonidentity swap
is a transport function but fails compatibility for either component section.
For naturality, take identity transport on maps from Spec k, and compose with the
swap on maps from Q. Restriction along a component Spec k to Q fails naturality.
These are errors below the unit level; the intended parent existence statement
is unchanged and is now proved with a real explicit construction.

## Old

```lean
theorem finiteLocalModels_transport_compatibility
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (transport : ∀ {W : Scheme.{u}} (a b : W ⟶ U.left),
      a ≫ U.hom = b ≫ U.hom →
      (Over.mk a ⟶ Over.mk Q.obj.hom) →
      (Over.mk b ⟶ Over.mk Q.obj.hom)) :
    ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
      (transport a.left b.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
        (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
          (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
      ((e.hom.app (op (Over.mk b))) s).down.left
```

## New

```lean
theorem finiteLocalModels_transport_compatibility
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
      (finiteLocalModels_transport T E U Q e a.left b.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
        (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
          (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
      ((e.hom.app (op (Over.mk b))) s).down.left
```

The new public definitions `finiteLocalModels_comparison` and
`finiteLocalModels_transport` construct their data by evaluating e and its inverse
on the universal Q-point and composing with a pullback lift. No unproved theorem
chooses data. The final packaging uses this constructed transport directly.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibilityDatum | F1 | Apply the corrected law to the explicit construction in the final packaging. |

`tools/downstream.py --uses` and a whole-library rg search find no external user
of this helper. There are 187 downstream modules through the import graph; all
continue to use the identical structure and parent theorem signatures. No forced
adaptation is needed. No target statement or definition used in its signature
changes: `FiniteLocalModelCompatibleTransport` keeps all its fields unchanged.

## Status

landed 20261012T144105-L-2092909 2026-10-12 (merge of deliver/F1/Sheaf.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibilityDatum)
