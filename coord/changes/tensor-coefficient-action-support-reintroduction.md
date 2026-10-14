# AlgebraicGeometry.Scheme.Modules.tensorGradedCoefficient_action_support

## Reason

The module and its DAG node were present when P3 received and read the assigned item,
but are absent on the baseline fetched by deliver3.py. Reintroduce the assigned theorem
with exactly its original signature and the proof written in this sandbox. The new
TensorKernelSectionProduct module is imported only by its proof. No existing definition,
statement or consumer interface is changed.

## Old

The fetched delivery base contains neither
`Sheaf.AlgebraicGeometry.TensorCoefficientActionSupport` nor
`lem-sc-tensor-coefficient-action-support`. The original assigned signature is the one
in the New section below; that signature was not edited.

## New

```lean
theorem tensorGradedCoefficient_action_support {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (d : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hrestrict : ∀ (U V : X.Opens) (a : V ⟶ U)
      (g : T.C.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      T.I.val.map a.op (σ U g y) = σ V (T.C.right.obj.map a.op g) (T.I.val.map a.op y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y) :
    ∃ v : kernel (tensorGradedUnit j (L.tensorPow d)) ⟶
        kernel (tensorGradedUnit j (L.tensorPow (n + d))),
      T.k d ≫ μ (tensorGradedSection T D 0 (tensorPowSection f 1)) =
        v ≫ T.k (n + d)
```

The theorem is proved, and both helpers in its module are private and proved.
The new public `tensorKernel_section_product` is also proved in its own module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TensorCoefficientActionSupport | P3 | Reintroduced with its originally assigned signature and a complete proof. |
| Sheaf.AlgebraicGeometry.TensorKernelSectionProduct | new module of P3 delivery | Proved helper, imported only by the item's proof. |

`tools/downstream.py Sheaf.AlgebraicGeometry.TensorCoefficientActionSupport --uses
 tensorGradedCoefficient_action_support` reports the module unknown at the fetched base.
There are no current downstream users to adapt. The earlier direct user
`TensorGradedCoefficientSheafAction` is now at an earlier implementation with no
import or use of the reintroduced theorem.

## Status

landed 20261014T034910-L-814924 2026-10-14 (merge of deliver/P3/Sheaf.AlgebraicGeometry.TensorCoefficientActionSupport)
