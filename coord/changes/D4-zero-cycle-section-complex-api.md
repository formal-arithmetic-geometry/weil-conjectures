# coefficientHomSectionComplex

## Reason

Write the same ordinary-section complex as the value of the uncurried global-Hom
bifunctor. This keeps the term identical to the existing global-cochain comparison
and prevents repeated expansion of the chosen Hom-complex functor during conversion.
Functor composition and uncurrying make the old and new bodies definitionally equal.

## Old

```lean
noncomputable def coefficientHomSectionComplex
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :=
  ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (homComplex.{c, v, max c v u, max c v u} (R := A) L
          ((coefficientHomResolution.{u, c, v} J A).obj M))
```

## New

```lean
noncomputable def coefficientHomSectionComplex
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :=
  ((Functor.uncurry.obj (homComplexFunctor.{c, v, max c v u, max c v u} (R := A)) ⋙
    (coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ)).obj
      (op L, (coefficientHomResolution.{u, c, v} J A).obj M))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientHomZeroClass | D4 | Same ordinary complex, cycle class and evaluation; optimized conversion. |

The complete use search and consumer validation are recorded in report.md. No
consumer signature changes. Targets depending on this definition are reopened for
statement review of the definitional equality.

## Status

landed 20261020T233114-L-894219 2026-10-20 (merge of deliver/D4/Sheaf.Paper.CoefficientHomZeroClass)
