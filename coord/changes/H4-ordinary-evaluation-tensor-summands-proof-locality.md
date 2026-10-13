# AlgebraicGeometry.exists_ordinaryEvaluation_tensor_summands

## Reason

Preflight conservatively classifies the added `open`, `variable`, and `attribute` commands
as an interface change. They support private proof helpers and local elaboration only.
In particular, making `Scheme.Modules.overEquiv` locally irreducible prevents expensive
unfolding of its sectionwise implementation. The combined file initially exceeded the
unchanged 60-second limit; the final file compiled cleanly in 50.3 seconds.
No existing declaration changes type or visibility. Both public imports remain identical.
The transparency attribute is explicitly local, and generic variables are enclosed in
sections that end before the original declaration. No public definition mentions a private
helper. No consumer or target statement changes meaning, and no adaptation is required.

## Old

The original namespace command block was:
```lean
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
```

The original theorem signature was:
```lean
theorem exists_ordinaryEvaluation_tensor_summands (X : Scheme.{u}) (U : X.Opens) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∃ m : L.CoreMonoidal,
      m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U ∧
      (∀ A B : localEvaluationModules X U,
        L.map (β_ A B).hom ≫ (m.μIso B A).inv =
          (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom) ∧
      ∀ P F : CochainComplex (localEvaluationModules X U) ℤ,
        ∃ c : T.obj (localEvaluationTensor X U P F) ≅
            pullbackTensorTotal U.toScheme (T.obj F) (T.obj (localEvaluationDual X U P)),
          ∀ (p q n : ℤ) (h : p + q = n),
            L.map (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
                (curriedTensor _) (.up ℤ) p q n h) ≫ c.hom.f n =
              (m.μIso (F.X p) ((localEvaluationDual X U P).X q)).inv ≫
                HomologicalComplex.ιMapBifunctor (T.obj F)
                  (T.obj (localEvaluationDual X U P)) (curriedTensor _) (.up ℤ) p q n h
```

## New

The namespace command block is now:
```lean
namespace AlgebraicGeometry

open BraidedCategory Functor MonoidalCategory.Functor

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
-- The proof uses the equivalence API, never its large sectionwise implementation.
attribute [local irreducible] Scheme.Modules.overEquiv
```

Private helpers use generic category variables inside `section Normalize` and
`section Descent`, each closed by its matching `end`. The scoped heartbeat settings on
the two scheme-level proofs have explanatory comments; they affect elaboration only.
The complete existing signature stays identical:
```lean
theorem exists_ordinaryEvaluation_tensor_summands (X : Scheme.{u}) (U : X.Opens) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∃ m : L.CoreMonoidal,
      m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U ∧
      (∀ A B : localEvaluationModules X U,
        L.map (β_ A B).hom ≫ (m.μIso B A).inv =
          (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom) ∧
      ∀ P F : CochainComplex (localEvaluationModules X U) ℤ,
        ∃ c : T.obj (localEvaluationTensor X U P F) ≅
            pullbackTensorTotal U.toScheme (T.obj F) (T.obj (localEvaluationDual X U P)),
          ∀ (p q n : ℤ) (h : p + q = n),
            L.map (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
                (curriedTensor _) (.up ℤ) p q n h) ≫ c.hom.f n =
              (m.μIso (F.X p) ((localEvaluationDual X U P).X q)).inv ≫
                HomologicalComplex.ιMapBifunctor (T.obj F)
                  (T.obj (localEvaluationDual X U P)) (curriedTensor _) (.up ℤ) p q n h
```
The two existing preadditivity instance definitions retain their exact signatures and
bodies. The original theorem now has a complete proof. No exported instance or attribute
is added.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.OrdinaryEvaluationTensorSummands --uses
AlgebraicGeometry.exists_ordinaryEvaluation_tensor_summands` reports 614 transitive
importers and two declaration mentions. The direct importer is
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTensorFormula`, whose existing application
receives exactly the same theorem statement. All transitive importers likewise retain
the same definitions and declarations; local proof commands do not propagate to them.
The existing target statements therefore need no renewed semantic review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationTensorSummands | H4 | Same signature; proof completed, private helpers and local elaboration commands added. |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTensorFormula | unclaimed | Same theorem application and meaning; no edit needed. |

## Status

landed 20261013T234512-L-2163357 2026-10-13 (merge of deliver/H4/Sheaf.AlgebraicGeometry.OrdinaryEvaluationTensorSummands)
