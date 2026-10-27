# WeilConjectures.CompletedModelSections.completedModelSectionsTransport

## Reason

The original finite-field telescope elaborates its module/sheaf data several times,
using definitionally equal canonical algebra structures from the concrete p-adic
field and the generic intermediate-field inclusion. Profiling isolates about ten
seconds of kernel checking at the `Realizes` hypothesis, even with a placeholder
proof. Beta-expand the coefficient parameters and specialize their entire telescope
as one expression. The statement then checks in about 0.1 seconds.

Every original binder, hypothesis and conclusion remains after beta reduction.
A separate Lean compilation checked the original signature verbatim by applying
the new theorem to all its original arguments (15.7 seconds including import and
original-signature checking). A second standalone Lean check proved equality of the
old and new proposition telescopes by `rfl` (22.2 seconds). The generic
constructibility adapter is private and
fully proved from `transport_eq`. All definitions used by the targets are unchanged.
The five declarations of `Challenge.lean` are unchanged.

## Old

```lean
theorem completedModelSectionsTransport (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (F G : Padic.FiniteCoefficientFields l Ω) (hFG : F ≤ G)
    (A : CochainComplex (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l F.val)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l G.val)) ℤ)
    (hA : IsModel l F.val A) (hC : IsModel l G.val C)
    (hK : sfIntegralConstructible l F.val (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l F.val).obj A)))
    (_hH : sfIntegralConstructible l G.val (Spec (.of D.k))
      (DerivedCategory.Q.obj ((model D l G.val).obj C)))
    (v : ((pointIntegralModuleTensor l F.val G.val
      (IntermediateField.inclusion hFG)).mapHomologicalComplex (.up ℤ)).obj A ⟶ C)
    (g : (completedOrdinaryScalarComplex l F.val G.val
      (IntermediateField.inclusion hFG) (Spec (.of D.k))).obj
        ((model D l F.val).obj A) ⟶ (model D l G.val).obj C)
    (_hg : Realizes D l F.val G.val (IntermediateField.inclusion hFG) A C v g) :
    transport D l F.val G.val (IntermediateField.inclusion hFG) hl A C hA hC
      ((pointIntegralConstructible_iff l F.val D hl _).mpr hK)
      (realizedMap D l F.val G.val (IntermediateField.inclusion hFG) A C g) =
        moduleMap l F.val G.val (IntermediateField.inclusion hFG) A C v ∧
    rationalTransport D l F.val G.val (IntermediateField.inclusion hFG) hl A C hA hC
      ((pointIntegralConstructible_iff l F.val D hl _).mpr hK)
      (realizedMap D l F.val G.val (IntermediateField.inclusion hFG) A C g) =
      rationalModuleMap l F.val G.val (IntermediateField.inclusion hFG) A C v
```

## New

```lean
theorem completedModelSectionsTransport (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (F G : Padic.FiniteCoefficientFields l Ω) (hFG : F ≤ G) :
    (fun (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
      (ι : E →ₐ[ℚ_[l]] L) ↦
      ∀ (A : CochainComplex (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l E)) ℤ)
        (C : CochainComplex (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l L)) ℤ)
        (hA : IsModel l E A) (hC : IsModel l L C)
        (hK : sfIntegralConstructible l E (Spec (.of D.k))
          (DerivedCategory.Q.obj ((model D l E).obj A)))
        (_hH : sfIntegralConstructible l L (Spec (.of D.k))
          (DerivedCategory.Q.obj ((model D l L).obj C)))
        (v : ((pointIntegralModuleTensor l E L
          ι).mapHomologicalComplex (.up ℤ)).obj A ⟶ C)
        (g : (completedOrdinaryScalarComplex l E L
          ι (Spec (.of D.k))).obj
            ((model D l E).obj A) ⟶ (model D l L).obj C)
        (_hg : Realizes D l E L ι A C v g),
        transport D l E L ι hl A C hA hC
          ((pointIntegralConstructible_iff l E D hl _).mpr hK)
          (realizedMap D l E L ι A C g) =
            moduleMap l E L ι A C v ∧
        rationalTransport D l E L ι hl A C hA hC
          ((pointIntegralConstructible_iff l E D hl _).mpr hK)
          (realizedMap D l E L ι A C g) =
          rationalModuleMap l E L ι A C v) F.val G.val (IntermediateField.inclusion hFG)
```

## Users

`python3 tools/downstream.py Sheaf.Paper.CompletedModelSectionsTransport --uses
WeilConjectures.CompletedModelSections.completedModelSectionsTransport` reports
zero downstream modules and one occurrence within the item itself.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedModelSectionsTransport | F9 | Definitionally equal coefficient telescope; all remaining declarations retain their signatures and meanings. |

## Status

landed 20261026T065707-L-3190075 2026-10-26 (merge of deliver/F9/Sheaf.Paper.CompletedModelSectionsTransport)
