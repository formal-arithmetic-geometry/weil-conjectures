# WeilConjectures.SemilinearSections.StrictCoefficientTensor.pure

## Reason

Respecting transparency during elaboration does not automatically identify the
commutative coefficient sheaf's sections with the underlying ring sheaf's sections
when synthesizing an implicit heterogeneous scalar action. Specify the underlying
ring explicitly. The resulting action and value are definitionally the original
ones, and the signature is identical. The large `Descent` structure also disables
unused generated size, injectivity and constructor-index helpers; its mathematical
fields and constructor are unchanged. No target changes meaning.

## Old

```lean
def pure {T : Sheaf J CommRingCat.{r}} (b : R ⟶ T)
    (d : Scalar J R b)
    (M : Mod.{c, v, r} J R) (U : Cᵒᵖ) (x : M.val.obj U) (s : T.obj.obj U) :
    (d.E.obj M).val.obj U :=
  s • (eqToHom (d.obj_eq M).symm).val.app U (extensionUnit b M U x)
```

## New

```lean
def pure {T : Sheaf J CommRingCat.{r}} (b : R ⟶ T)
    (d : Scalar J R b)
    (M : Mod.{c, v, r} J R) (U : Cᵒᵖ) (x : M.val.obj U) (s : T.obj.obj U) :
    (d.E.obj M).val.obj U :=
  @SMul.smul ((ring J T).obj.obj U) _ inferInstance s
    ((eqToHom (d.obj_eq M).symm).val.app U (extensionUnit b M U x))
```

## Users

`tools/downstream.py Sheaf.Algebra.Homology.StrictCoefficientTensorDescent --uses pure`
found zero downstream modules and only this module mentioning the declaration.
The DAG parents still require the node; none is removed or weakened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.StrictCoefficientTensorDescent | H3 | identical action and signature |

## Status

landed 20261025T180719-L-4023353 2026-10-25 (merge of deliver/H3/Sheaf.Algebra.Homology.StrictCoefficientTensorDescent)
