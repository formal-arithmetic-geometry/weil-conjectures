# internalHom_filtered_continuity proof helper scopes

## Reason

The proof adds generic private helpers before the original site variables. They
need two independent generic universes (`w`, `a`), the HomologicalComplex and
MonoidalCategory namespace openings, and local section variables. The preflight
classifies these commands conservatively as an interface change, requiring this
record. Every added declaration is a proved private theorem; no exported
signature, definition, instance, attribute or public import changes.

## Old

The file's existing universe and namespace-opening commands were:

```lean
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite
```

The existing public theorem signature was:

```lean
theorem internalHom_filtered_continuity (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    [HasExactColimitsOfShape I (Modules.{u, v, r} J R)]
    (T : I ⥤ Modules.{u, v, r} J R)
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty
      (T.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hcont : Continuous.{u, v, r} J R (I := I) P)
    (b : ℤ) (hL : ∀ n : ℤ, n < b → IsZero (L.X n)) :
    QuasiIso (roofDenominator.{u, v, r} J R P L (colimit T)) ∧
    QuasiIso (colimit.post T
      (tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P)) ∧
    IsIso (colimit.post T
      (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)))
```

## New

The corresponding universe and namespace-opening commands are:

```lean
universe u v r w a
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex MonoidalCategory
```

The new helper variables occur inside sections `Exactness`, `Transport`,
`TensorMap` and `Assemble`, all closed before the original site variables. These
sections contain only private proved theorems. The existing public theorem
signature remains verbatim:

```lean
theorem internalHom_filtered_continuity (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    [HasExactColimitsOfShape I (Modules.{u, v, r} J R)]
    (T : I ⥤ Modules.{u, v, r} J R)
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty
      (T.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hcont : Continuous.{u, v, r} J R (I := I) P)
    (b : ℤ) (hL : ∀ n : ℤ, n < b → IsZero (L.X n)) :
    QuasiIso (roofDenominator.{u, v, r} J R P L (colimit T)) ∧
    QuasiIso (colimit.post T
      (tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P)) ∧
    IsIso (colimit.post T
      (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)))
```

## Users

`tools/downstream.py Sheaf.Paper.InternalHomFilteredContinuity --uses
internalHom_filtered_continuity` lists exactly one downstream module. Its sole
application uses the unchanged theorem with the same explicit arguments and
extracts the same three conjuncts. Private helper declarations and their generic
section variables cannot enter its signatures. Namespace-opening commands are
file-local. No target meaning or consumer source needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalHomFilteredContinuity | M1 | One hole closed; private proof helpers and local scopes added; public signature unchanged. |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | R3 | Existing application and public interface unchanged; no adaptation. |

## Status

landed 20261021T012406-L-2184948 2026-10-21 (merge of deliver/M1/Sheaf.Paper.InternalHomFilteredContinuity)
