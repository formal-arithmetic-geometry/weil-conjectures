# WeilConjectures.IntegralAmbient.integralAmbientOperationModels

## Reason

The original signature forces Lean to repeatedly normalize large cochain tensor,
Roos, and derived-category object constructions while comparing endpoints. A complete
proof using the direct interface checked but took 92.7 seconds, exceeding the file
limit. The new interface captures the existing category data once, constructs all
operations and their proved compatibility laws as `rawAmbientPackage`, and uses one
shared record `ambientPackage`. The latter is chosen from the **proved** theorem
that equality to this explicitly constructed record determines a unique value;
`ambientPackage_eq` proves literal equality of the entire record to that construction.
Thus every functor, comparison and augmentation is exactly the recorded one.
There is no selection from an unproved arbitrary existence theorem and no new hole.

The carrier and good-complex types reduce to the original ones through
`ambientTensorPresentation`. Named good localization and lift functors share their
endpoints. In particular, `modelPullUnitMap` and `modelTensorUnitMap` are the images
of the same quotient Roos units followed by the same strict tower maps. The tensor
representative is the component of the exact recorded tensor model comparison.
The theorem's hypotheses, universal-derived condition, good-object isomorphisms,
completion comparisons, strict tower normalizations and augmentation equations are
all retained. These changes concern S7's own non-target module; no adopted source
module and no statement in `Challenge.lean` is changed. Definitions used by targets
receive renewed statement/definition review. The final file compiled in 39.4 seconds.

## Old

```lean
theorem integralAmbientOperationModels {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (ε : DerivedCategory.Q ⋙ F ⟶ pullComplex l E f ⋙ DerivedCategory.Q)
      (α : F ⋙ IntegralOnSlice.completion l E X none ≅ integralDerivedPullback l E f),
      F.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)) ∧
      (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        IsIso (ε.app P.obj)) ∧
      (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        α.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralDerivedPullbackComparison l E f).hom.app P =
          (IntegralOnSlice.completion l E X none).map (ε.app P.obj) ≫
            (IntegralOnSlice.completionComparison l E X none).hom.app
              ⟨(pullComplex l E f).obj P.obj, pull_good l E f P.obj P.property⟩ ≫
            DerivedCategory.Q.map
              (integralOperationsRoosFunctor.map ((pullTowerIso l E f).hom.app P.obj))) ∧
      (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (IntegralOnSlice.completionUnit l E X none).app (F.obj (DerivedCategory.Q.obj P.obj)) ≫
            α.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralDerivedPullbackComparison l E f).hom.app P =
          ε.app P.obj ≫ DerivedCategory.Q.map (pullOperationUnit l E f P.obj)) ∧
      ∀ W : Scheme.{t}, W = X ∨ W = Y →
        ∃ β : (IntegralOnSlice.duality l E W none).closed.tensor ⋙
            IntegralOnSlice.completion l E W none ≅ integralCompletedTensor l E W,
          (∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
            β.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
                (integralCompletedTensorComparison l E W).hom.app (P, Q) =
              (IntegralOnSlice.completion l E W none).map
                (tensorRepresentative l E W P Q).inv ≫
              (IntegralOnSlice.completionComparison l E W none).hom.app
                ⟨_, tensor_good l E W P.obj Q.obj P.property Q.property⟩ ≫
              DerivedCategory.Q.map (integralOperationsRoosFunctor.map
                ((tensorTowerIso l E W).hom.app (P.obj, Q.obj)))) ∧
          (∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
            (IntegralOnSlice.completionUnit l E W none).app
                ((IntegralOnSlice.duality l E W none).closed.tensor.obj
                  (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
                β.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
                (integralCompletedTensorComparison l E W).hom.app (P, Q) =
              (tensorRepresentative l E W P Q).inv ≫
                DerivedCategory.Q.map (tensorOperationUnit l E W P.obj Q.obj))
```

## New

```lean
theorem integralAmbientOperationModels {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ (F : ambientD l E Y ⥤
        ambientD l E X)
      (ε : modelQ l E Y ⋙ F ⟶ modelPullComplex l E f ⋙ modelQ l E X)
      (α : F ⋙ modelCompletion l E X ≅ modelPull l E f),
      F.IsLeftDerivedFunctor ε
        (ambientQuasiIso l E Y) ∧
      (∀ P : (ambientGood l E Y).FullSubcategory,
        IsIso (ε.app P.obj)) ∧
      (∀ P : (ambientGood l E Y).FullSubcategory,
        α.hom.app ((modelGoodLocalization l E Y).obj P) ≫
            (modelPullComparison l E f).hom.app P =
          (modelCompletion l E X).map (ε.app P.obj) ≫
            (modelCompletionComparison l E X).hom.app
              ((modelPullGoodLift l E f).obj P) ≫
            modelPullTowerMap l E f P.obj) ∧
      (∀ P : (ambientGood l E Y).FullSubcategory,
        (modelCompletionUnit l E X).app (F.obj ((modelGoodLocalization l E Y).obj P)) ≫
            α.hom.app ((modelGoodLocalization l E Y).obj P) ≫
            (modelPullComparison l E f).hom.app P =
          ε.app P.obj ≫ modelPullUnitMap l E f P.obj) ∧
      ∀ W : Scheme.{t}, W = X ∨ W = Y →
        ∃ β : (modelOrdinaryTensor l E W) ⋙
            modelCompletion l E W ≅ modelCompletedTensor l E W,
          (∀ P Q : (ambientGood l E W).FullSubcategory,
            β.hom.app
              (((modelGoodLocalization l E W).prod (modelGoodLocalization l E W)).obj (P, Q)) ≫
                (modelTensorComparison l E W).hom.app (P, Q) =
              (modelCompletion l E W).map
                (tensorRepresentative l E W P Q).inv ≫
              (modelCompletionComparison l E W).hom.app
                ((modelTensorGoodLift l E W).obj (P, Q)) ≫
              modelTensorTowerMap l E W P.obj Q.obj) ∧
          (∀ P Q : (ambientGood l E W).FullSubcategory,
            (modelCompletionUnit l E W).app
                ((modelOrdinaryTensor l E W).obj
                  (((modelGoodLocalization l E W).prod (modelGoodLocalization l E W)).obj (P, Q))) ≫
                β.hom.app
              (((modelGoodLocalization l E W).prod (modelGoodLocalization l E W)).obj (P, Q)) ≫
                (modelTensorComparison l E W).hom.app (P, Q) =
              (tensorRepresentative l E W P Q).inv ≫
                modelTensorUnitMap l E W P.obj Q.obj)
```

## Users

`tools/downstream.py Sheaf.Paper.IntegralAmbientOperationModels --uses
integralAmbientOperationModels tensorRepresentative` reports 40 modules downstream
by imports, and one actual declaration user for each changed name: this module.
A source and quarantine search distinguishes similarly named declarations in other
namespaces; none is a use of these changed declarations. The returned review additionally
identified an `import all` instance-environment consumer. The proof-import isolation
documented in `S7-point-integral-tensor-chain-instance-repair.md` removes the leak
at its source; no consumer adaptation is delivered. All original operation-interface
declarations are attached to the same node.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.IntegralAmbientOperationModels` | S7 | uses the exact shared operation interface; original mathematical content retained |
| `Sheaf.Paper.PointIntegralTensorChain` | unclaimed; quarantined | preserved unchanged; the proof-import boundary now hides the two broad instances |

## Status

landed 20261026T111926-L-1778770 2026-10-26 (merge of deliver/S7/Sheaf.Paper.IntegralAmbientOperationModels)
