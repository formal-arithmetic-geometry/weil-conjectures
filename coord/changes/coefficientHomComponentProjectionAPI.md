# WeilConjectures.coefficientHomComponent

## Reason

Use the existing `homComplexπ` API for the recorded product projection. Expanding the
original nested choice specification repeatedly makes component calculations expensive.
`homComplex_projections_exists` states exactly the `Classical.choose_spec` proposition
of `homComplex_exists`, with its chosen functor named `homComplexFunctor`. Thus the old
and new implementations select the same data: their existence proofs are equal by proof
irrelevance. The definition's type, evaluation convention and chosen Hom complex are
unchanged. This is an implementation change, not a new choice of projections.

The module adds a public import of `HomComplexComponents`, which the definition now uses.
No source-library module is changed. No target statement is changed. The definition is
used by target statements, so this record makes its implementation available for the
independent semantic review required by AGENTS.md §4.

## Old

```lean
noncomputable def coefficientHomComponent
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex.{c, v, max c v u, max c v u} (R := A) L M).X n ⟶
      SheafOfModules.homObj (R := A) (L.X p) (M.X q) :=
  (homComplex_exists.{c, v, max c v u, max c v u}
    (R := A)).choose_spec.choose L M n p q h
```

## New

```lean
noncomputable def coefficientHomComponent
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex.{c, v, max c v u, max c v u} (R := A) L M).X n ⟶
      SheafOfModules.homObj (R := A) (L.X p) (M.X q) :=
  homComplexπ.{c, v, max c v u, max c v u} (J := J) (R := A) L M n p q h
```

## Users

`python3 tools/downstream.py Sheaf.Paper.CoefficientHomRepresentativeEvaluation
--uses coefficientHomComponent` identifies the following direct declaration users.
Each keeps the same statement and meaning. All seven external direct consumers, including
the item module, compiled against the changed definition without signature adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses | S6 | Same projection; no signature adaptation. |
| Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose | M1 | Same projection; no signature adaptation. |
| Sheaf.CategoryTheory.RingedSiteDualityMaps | Z6 | Same projection; no signature adaptation. |
| Sheaf.Paper.CoefficientHomRepresentativeEvaluation | unclaimed | Same projection; no signature adaptation. |
| Sheaf.Paper.CoefficientHomZeroClass | D4 | Same projection; no signature adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Same projection; no signature adaptation. |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | C1 | Same projection; no signature adaptation. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Same projection; no signature adaptation. |

## Status

landed 20261020T211638-L-3482443 2026-10-20 (merge of deliver/C1/Sheaf.Paper.DerivedInternalHomFilteredColimit)
