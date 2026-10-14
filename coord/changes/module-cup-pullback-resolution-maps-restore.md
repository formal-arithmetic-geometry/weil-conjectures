# AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_resolution_maps

## Reason

The dispatcher supplied this module and its DAG node, and both were read from the shared
checkout at the beginning of the task. During the task the checkout changed. The required
delivery dry run fetched a baseline that contains neither the module nor the node and
therefore classified their restoration as a new public interface. This record documents
that classification; the dispatched theorem signature is preserved exactly.

The complete proof constructs additive global maps from sheaf cochain f-maps, proves their
cohomology class equations using a general comparison proved in the delivery, and uses target
coefficient naturality for the tensor coefficient. The only new hole is strictly the
simultaneous augmented pairing construction. The restored node records E1's restoration
provenance and the actual searches run by this task.

## Old

The fetched delivery baseline has no file or declaration. The dispatched version carried
this signature, with its proof `:= by sorry`:

```lean
theorem moduleCup_pullback_resolution_maps (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) :
    ∃ (D : CupResolutionPairing F G)
      (E : CupResolutionPairing ((tensorPullback f).obj F) ((tensorPullback f).obj G))
      (l : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K ⟶
      ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.left.K)
      (r : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K ⟶
      ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.right.K)
      (t : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K ⟶
      ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.target.K),
      (∀ (n : ℕ)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc n).moduleCatLeftHomologyData.K)
        (a' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.left.K).sc n).moduleCatLeftHomologyData.K),
        a'.val = l.f n a.val →
          E.left.class n a' =
            moduleCohomologyPullback f F n (D.left.class n a)) ∧
      (∀ (n : ℕ)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc n).moduleCatLeftHomologyData.K)
        (b' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.right.K).sc n).moduleCatLeftHomologyData.K),
        b'.val = r.f n b.val →
          E.right.class n b' =
            moduleCohomologyPullback f G n (D.right.class n b)) ∧
      (∀ (n : ℕ)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc n).moduleCatLeftHomologyData.K)
        (c' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.target.K).sc n).moduleCatLeftHomologyData.K),
        c'.val = t.f n c.val →
          E.target.class n c' =
            (RingedSpace.moduleCohomology X'.toRingedSpace n).map
              ((Classical.choose (module_pullback_tensor f)) F G).hom
              (moduleCohomologyPullback f (@id X.Modules (F ⊗ G)) n
                (D.target.class n c))) ∧
      (∀ (p q : ℕ) (a : Γ(D.left.K.X p, ⊤)) (b : Γ(D.right.K.X q, ⊤)),
        t.f (p + q) (D.pair p q ⊤ a b) =
          E.pair p q ⊤ (l.f p a) (r.f q b))
```

## New

Restored the exact same signature with a complete proof from
`moduleCup_pullback_augmented_pairings`, `cupResolution_class_fmap`, and
`moduleCohomologyFMap_target_naturality`. The signature is:

```lean
theorem moduleCup_pullback_resolution_maps (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) :
    ∃ (D : CupResolutionPairing F G)
      (E : CupResolutionPairing ((tensorPullback f).obj F) ((tensorPullback f).obj G))
      (l : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K ⟶
      ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.left.K)
      (r : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K ⟶
      ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.right.K)
      (t : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K ⟶
      ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.target.K),
      (∀ (n : ℕ)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc n).moduleCatLeftHomologyData.K)
        (a' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.left.K).sc n).moduleCatLeftHomologyData.K),
        a'.val = l.f n a.val →
          E.left.class n a' =
            moduleCohomologyPullback f F n (D.left.class n a)) ∧
      (∀ (n : ℕ)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc n).moduleCatLeftHomologyData.K)
        (b' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.right.K).sc n).moduleCatLeftHomologyData.K),
        b'.val = r.f n b.val →
          E.right.class n b' =
            moduleCohomologyPullback f G n (D.right.class n b)) ∧
      (∀ (n : ℕ)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc n).moduleCatLeftHomologyData.K)
        (c' : ((((RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.target.K).sc n).moduleCatLeftHomologyData.K),
        c'.val = t.f n c.val →
          E.target.class n c' =
            (RingedSpace.moduleCohomology X'.toRingedSpace n).map
              ((Classical.choose (module_pullback_tensor f)) F G).hom
              (moduleCohomologyPullback f (@id X.Modules (F ⊗ G)) n
                (D.target.class n c))) ∧
      (∀ (p q : ℕ) (a : Γ(D.left.K.X p, ⊤)) (b : Γ(D.right.K.X q, ⊤)),
        t.f (p + q) (D.pair p q ⊤ a b) =
          E.pair p q ⊤ (l.f p a) (r.f q b))
```

Added only the two supporting modules and their nodes described in the report. No declaration
of Challenge.lean, and no existing definition or signature, changes.

## Users

`tools/downstream.py --allow-missing --uses moduleCup_pullback_resolution_maps` reports
zero downstream modules and zero textual users in the fetched baseline. The dispatched
snapshot had a user in `Sheaf.Paper.CechCupPullbackCompat`; its use fits the preserved signature
without adaptation. No file belonging to another holder is adapted in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupPullbackResolutionMaps | E1 | Restore dispatched interface and add proof. |

## Status

landed 20261014T033104-L-603179 2026-10-14 (merge of deliver/E1/Sheaf.Paper.ModuleCupPullbackResolutionMaps)
