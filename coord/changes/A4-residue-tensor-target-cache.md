# CategoryTheory.Functor.tensorModelTarget

## Reason

Cache the existing tensor-model target to prevent concrete sheaf specializations from
expanding the derived braiding construction. Its construction body is unchanged. A proved
formula supplies the expansion needed for the generic tensor calculation. The module is
unclaimed; no existing signature or visibility changes. Target definition review is reopened
for maintainer verification that the data are unchanged.

## Old

```lean
@[irreducible] noncomputable def tensorModelTarget (B : C) (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P) ⊗
        F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  (β_ (F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B))
    (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P))).inv ≫
    ((F.leftDerivedFunctor.map (tensorModelCoefficientIso B).hom ≫
      F.leftDerivedFunctorCounit.app (tensorModelCoefficient B)) ⊗ₘ
      F.leftDerivedFunctorCounit.app P) ≫
    LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)
```

## New

```lean
@[no_expose, irreducible]
noncomputable def tensorModelTarget (B : C) (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P) ⊗
        F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  (β_ (F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B))
    (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P))).inv ≫
    ((F.leftDerivedFunctor.map (tensorModelCoefficientIso B).hom ≫
      F.leftDerivedFunctorCounit.app (tensorModelCoefficient B)) ⊗ₘ
      F.leftDerivedFunctorCounit.app P) ≫
    LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)

/-- The explicit formula for the cached tensor-model target.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-model)
Proof. The formula is the defining composite, so the identity is reflexive. -/
theorem tensorModelTarget_eq (B : C) (P : HomotopyCategory C (.up ℤ)) :
    tensorModelTarget F B P =
  (β_ (F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B))
    (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P))).inv ≫
    ((F.leftDerivedFunctor.map (tensorModelCoefficientIso B).hom ≫
      F.leftDerivedFunctorCounit.app (tensorModelCoefficient B)) ⊗ₘ
      F.leftDerivedFunctorCounit.app P) ≫
    LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P) := by
  unfold tensorModelTarget
  rfl
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Cache the same target and prove its defining formula; its existing invertibility proof still unfolds it locally. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | A4 | Rewrite the formula in the generic calculation. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Existing invertibility API and mathematical statement unchanged. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | Existing invertibility API and mathematical statement unchanged. |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | unclaimed | Its normalization unfolds the cached tensor target; statement and data unchanged. |


`tools/downstream.py Sheaf.Paper.IntegralResidueTensorModel --uses tensorModelTarget`
finds only the defining module as a textual user. There are 36 transitive importers;
their statements and data do not change. The full importer list is the table in
`A4-residue-derived-monoidal-cache.md`, omitting IntegralResidueTensorModel itself.
No consumer unfolds the target outside its defining module. No adaptation is needed.

## Status

landed 20261017T144415-L-4152973 2026-10-17 (merge of deliver/A4/Sheaf.Paper.IntegralResidueTensorRouteModel)
