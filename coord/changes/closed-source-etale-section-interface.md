# AlgebraicGeometry.ClosedSourceSiteTensor.etaleSupportSections

## Reason

Give the existing etale closed exchange its native supported-constant source and
 target in the proved data wrapper `etaleExchangeNative`. Its body is the identical
`Etale.closedConstantPullbackAdjoint`. The section map uses this wrapper before
terminal evaluation. This avoids conversion between the monoidal-unit and
constant-sheaf presentations after evaluating a concrete sheaf. Unfolding the
wrapper gives the previous definition verbatim. No map, universe, hypothesis, or
target signature changes. This reached definition requires independent review.

## Old

```lean
def etaleSupportSections (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (Y : X.ProEt) :
    ((pull A false Y.hom).obj (supported A false i)).obj.obj
        (op (Scheme.Etale.mk (𝟙 Y.left))) ⟶
      (constant A false (pullback Y.hom i)).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback Y.hom i)))) :=
  (Etale.closedConstantPullbackAdjoint A i Y.hom).hom.app
      (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
    (constant A false (pullback Y.hom i)).obj.map
      (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y.left) (pullback.fst Y.hom i)))
        (Category.comp_id _) :
        (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst Y.hom i)).obj
          (Scheme.Etale.mk (𝟙 Y.left)) ≅
            Scheme.Etale.mk (𝟙 (pullback Y.hom i))).inv.op
```

## New

```lean
/-- The prescribed etale exchange with the common supported-constant interface.
Source: Stacks 03S6; the existing etale closed constant pullback adjoint.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def etaleExchangeNative (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    (pull A false v).obj (supported A false i) ⟶
      supported A false (pullback.fst v i) :=
  Etale.closedConstantPullbackAdjoint A i v

/-- The specified etale closed exchange followed by terminal direct-image evaluation.
Source: lem-pur-etale-closed-constant-tensor; Stacks 03S6
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def etaleSupportSections (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (Y : X.ProEt) :
    ((pull A false (X := Y.left) Y.hom).obj (supported A false i)).obj.obj
        (op (Scheme.Etale.mk (𝟙 Y.left))) ⟶
      (constant A false (pullback Y.hom i)).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback Y.hom i)))) :=
  (etaleExchangeNative A (X' := Y.left) i Y.hom).hom.app
      (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
    (constant A false (pullback Y.hom i)).obj.map
      (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y.left) (pullback.fst Y.hom i)))
        (Category.comp_id _) :
        (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst Y.hom i)).obj
          (Scheme.Etale.mk (𝟙 Y.left)) ≅
            Scheme.Etale.mk (𝟙 (pullback Y.hom i))).inv.op
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison | J5 | Definitionally identical section map, with the native exchange interface. |

## Status

landed 20261026T001858-L-37735 2026-10-26 (merge of deliver/J5/Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison)
