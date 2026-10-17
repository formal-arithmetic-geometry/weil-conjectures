# CategoryTheory.Functor.tensorModelTargetWith and the canonical model

## Reason

Expanding the concrete pullback's left-derived implementation in the core causes
expensive repeated instance conversion. The model's four-map construction can be
expressed using any named derived functor G and counit gamma. The original generic
target remains its specialization. The paper target keeps its original constructor.
The kernel checks its definitional equality with the named pullback specialization.

## Old

The old local braiding was the existing `DerivedMonoidal.braidedCategory Qh
(HomotopyCategory.quasiIso D (.up ℤ))`. The old coefficient and target were:

```lean
noncomputable def tensorModelCoefficientIso (B : C) :
    (DerivedCategory.singleFunctor C 0).obj B ≅
      DerivedCategory.Qh.obj (tensorModelCoefficient B) :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).app B ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app _
```

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

```lean
@[irreducible]
noncomputable def residueExchangeTensorModelTarget :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P) ⊗
        (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
          (residueExchangeCoefficient ℓ E Y) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  unfold residueExchangeUpperStar
  exact Functor.tensorModelTarget (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeOrdinaryCoefficient ℓ E Y) P
```

## New

```lean
noncomputable def tensorModelCoefficientIso (B : C) :
    (DerivedCategory.singleFunctor C 0).obj B ≅
      DerivedCategory.Qh.obj (tensorModelCoefficient B) :=
  CategoryTheory.homotopySingleComparisonIso B
```

```lean
@[irreducible] noncomputable def tensorModelTargetWith
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ G ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (B : C) (P : HomotopyCategory C (.up ℤ)) :
    G.obj (DerivedCategory.Qh.obj P) ⊗
        G.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  (β_ (G.obj ((DerivedCategory.singleFunctor C 0).obj B))
    (G.obj (DerivedCategory.Qh.obj P))).inv ≫
    ((G.map (tensorModelCoefficientIso B).hom ≫ γ.app (tensorModelCoefficient B)) ⊗ₘ
      γ.app P) ≫
    LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)
```

```lean
@[irreducible] noncomputable def tensorModelTarget (B : C) (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P) ⊗
        F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  tensorModelTargetWith F F.leftDerivedFunctor F.leftDerivedFunctorCounit B P
```

```lean
@[irreducible]
noncomputable def residueExchangeTensorModelTarget :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P) ⊗
        (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
          (residueExchangeCoefficient ℓ E Y) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  unfold residueExchangeUpperStar
  exact Functor.tensorModelTarget (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeOrdinaryCoefficient ℓ E Y) P
```



The shared derived braiding is exactly the old construction, now named in the
presentation module and registered locally. The original local declaration name
`instBraidedCategoryDerivedCategory_sheaf` and body are retained. The old compiler
also factored out a closed proof named
`instBraidedCategoryDerivedCategory_sheaf._proof_1 : IsRightCancelAdd ℤ`.
Its type and body were read from the published interface. Existing compiled
consumer signatures still refer to it; moving the shared braiding otherwise
removed that name and gave a kernel unknown-constant error. The explicit
compatibility theorem proves that same fact by the existing Mathlib instance.
The auxiliary-name linter is suppressed only at this compatibility declaration.
No assumption or axiom is added. Reducible abbreviations name the existing
derived/homotopy monoidal structures; no global instance is exported.

`tensorModelCoefficientIso_counit` is fully proved using the exact-functor
comparison and naturality of the single/quotient isomorphisms. The invertibility
proof of the original target unfolds its new wrapper too. Local irreducibility
of the generic derived functors prevents accidental expansion during elaboration.

## Users

The table includes every direct use of the changed coefficient and target maps,
and the tensor presentation users sharing this braiding. All existing signatures
and visibility in this module are retained. The wrapper expands to the identical
four maps, and the paper constructor is unchanged. The core's equivalent named
counit let body is recorded separately. Affected target definition review reopens.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | Canonical comparisons and named balanced counit; data constructed explicitly. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Shared braiding and coefficient comparison; same tensor maps. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | Proved defining equation and coefficient-counit equation. |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | A3 | Uses the proved generic normalization and the same actual constructors. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | Same core statement and canonical maps. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | Consumer check of the same canonical tensor presentation/model. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | Consumer check of the same canonical tensor presentation/model. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Consumer check of the same canonical tensor presentation/model. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | B3 | Consumer check; no signature or visibility change allowed. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Consumer check of the same canonical tensor presentation. |

## Status

landed 20261017T213021-L-1678945 2026-10-17 (merge of deliver/A3/Sheaf.Paper.IntegralResidueTensorPullCounitCore)
