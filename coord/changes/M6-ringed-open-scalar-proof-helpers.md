# SheafOfModules.RingedOpenScalar.comparison

## Reason

Stage-3 preflight classifies the new section-variable commands around private
proof helpers as changing what other modules see and requires this record.
These variables bind only new private declarations. Every existing declaration
signature and definition body is preserved; the only existing theorem body
changed is `comparison`. The single new import is private:
`Sheaf.SixFunctors.ExactLocalizationInverseMate`.

There are no new global instances. Invertibility of the private constructed map
is a private proved theorem, installed as an instance only inside the private
isomorphism construction. No target definition or public statement changes.

## Old

The following signature is preserved verbatim. Its old proof was `by sorry`.

```lean
theorem comparison :
    ∃ p : extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U ⋙
        PresheafOfModules.restrictScalars
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom ≅
      sliceScalars.{c, v, r} U a ⋙
        extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} R) U,
    (∀ (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
      (V : Cᵒᵖ) (x : extensionByZeroPresheafSection (rings.{c, v, r} S) U N V),
      (p.hom.app N).app V x = x) ∧
    ∃ e : localizedSystemExtension.{c, v, r} S U ⋙ scalars.{c, v, r} a ≅
      sliceScalars.{c, v, r} U a ⋙ localizedSystemExtension.{c, v, r} R U,
    (∀ (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
      (V : Cᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))),
      (e.hom.app N).val.app V (generator.{c, v, r} U S N V phi x) =
        generator.{c, v, r} U R ((sliceScalars.{c, v, r} U a).obj N) V phi x) ∧
    Equations e (restrictionIso.{c, v, r} U a)
      (localizedSystemAdjunction.{c, v, r} S U)
      (localizedSystemAdjunction.{c, v, r} R U) ∧
    transportedEquations.{c, v, r, w} U a e
```

The private helpers and their private section variables were absent.

## New

The same signature, verbatim:

```lean
theorem comparison :
    ∃ p : extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} S) U ⋙
        PresheafOfModules.restrictScalars
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a).hom ≅
      sliceScalars.{c, v, r} U a ⋙
        extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} R) U,
    (∀ (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
      (V : Cᵒᵖ) (x : extensionByZeroPresheafSection (rings.{c, v, r} S) U N V),
      (p.hom.app N).app V x = x) ∧
    ∃ e : localizedSystemExtension.{c, v, r} S U ⋙ scalars.{c, v, r} a ≅
      sliceScalars.{c, v, r} U a ⋙ localizedSystemExtension.{c, v, r} R U,
    (∀ (N : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U))
      (V : Cᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))),
      (e.hom.app N).val.app V (generator.{c, v, r} U S N V phi x) =
        generator.{c, v, r} U R ((sliceScalars.{c, v, r} U a).obj N) V phi x) ∧
    Equations e (restrictionIso.{c, v, r} U a)
      (localizedSystemAdjunction.{c, v, r} S U)
      (localizedSystemAdjunction.{c, v, r} R U) ∧
    transportedEquations.{c, v, r, w} U a e
```

Its proof is complete. Private generic helpers establish the mate equations and
their complex, tower, and derived versions. Private concrete helpers construct
the identity presheaf comparison, its sheafification comparison, and prove
generator normalization. Section variables affect only these private helpers.
The original concrete-variable command is retained verbatim after the generic
helper section.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedOpenScalarAdjunction | M6 | Its remaining proof is filled; public interface unchanged. |
| Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars | unclaimed | No interface change; no adaptation required. |
| Sheaf.CategoryTheory.ToposFiniteFreeCompactConstituents | unclaimed | No interface change; no adaptation required. |

`tools/downstream.py Sheaf.CategoryTheory.RingedOpenScalarAdjunction --uses comparison`
reports these two downstream modules; neither mentions `comparison`. Neither
module has a current claim record. No existing definition changes.

## Status

landed 20261023T231839-L-3651389 2026-10-23 (merge of deliver/M6/Sheaf.CategoryTheory.RingedOpenScalarAdjunction)
