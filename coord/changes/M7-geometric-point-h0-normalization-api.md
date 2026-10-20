# AlgebraicGeometry.Etale.geometricPointDerivedSectionsIso and H⁰ isomorphisms

## Reason

The kernel repeatedly unfolds the geometric stalk's colimit when checking nested canonical
derived adjunctions and their H⁰ normalization. Name the generic canonical constructions and
provide proved counit and H⁰ APIs. The geometric-point proof specializes these APIs and
checks the actual section-to-germ map separately.

All three replacements below are definitionally the original constructions: unfold
`Adjunction.normalizedDerivedRightAdjointIso`, `Functor.mapSingleRightDerivedH0Iso`, and
`Functor.singleRightDerivedH0Iso`, together with the existing geometric-point adjunction
aliases, to recover the old bodies. No functor, morphism, chosen object, hypothesis, or
conclusion changes. The source library is unchanged. The generic definitions contain actual
composites, with no deferred data; their irreducibility and proved APIs avoid repeated
concrete reduction. The original signatures and public imports stay verbatim.

## Old

```lean
noncomputable def geometricPointDerivedSectionsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
        (geometricPointStalk Ω).mapDerivedCategory ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z :=
  (((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.comp
      (geometricPointSectionsImageAdjunction Ω h)).ofNatIsoLeft
        (geometricPointSectionsConstantsIso Ω h)).rightAdjointUniq
    (geometricPointSectionsConstantAdjunction Z)

noncomputable def geometricPointSectionsImageH0Iso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
          (geometricPointStalk Ω).mapDerivedCategory).obj
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (geometricPointStalk Ω).obj ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) :=
  ((geometricPointStalk Ω).mapDerivedCategoryHomologyFunctorIso 0).symm.app _ ≪≫
    (geometricPointStalk Ω).mapIso
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h
        |>.homologyRightDerivedFunctorObjSingleFunctorIso G 0) ≪≫
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedZeroIsoSelf.app G)

noncomputable def geometricPointSectionsGlobalH0Iso (Z : Scheme.{u})
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G :=
  (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    |>.homologyRightDerivedFunctorObjSingleFunctorIso G 0) ≪≫
    (Sheaf.Γ Z.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).rightDerivedZeroIsoSelf.app G
```

## New

```lean
noncomputable def geometricPointDerivedSectionsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
        (geometricPointStalk Ω).mapDerivedCategory ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z :=
  Adjunction.normalizedDerivedRightAdjointIso (geometricPointSectionsStalkAdjunction Ω)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
    (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)

noncomputable def geometricPointSectionsImageH0Iso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
          (geometricPointStalk Ω).mapDerivedCategory).obj
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (geometricPointStalk Ω).obj ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) :=
  (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapSingleRightDerivedH0Iso
    (geometricPointStalk Ω) G

noncomputable def geometricPointSectionsGlobalH0Iso (Z : Scheme.{u})
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G :=
  (Sheaf.Γ Z.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).singleRightDerivedH0Iso G
```

The module adds a public import of `Sheaf.CategoryTheory.SingleAdjunctionComparison`,
which publicly imports the canonical H⁰ constructions. This is needed by the definitions.
Their new generic counit, augmentation, and normalized-H⁰ theorems are all proved.

## Users

`tools/downstream.py` lists the following two downstream modules and the declaration uses.
Only the item uses the H⁰ names. The projection-comparison consumer uses the derived
comparison as an argument to the categorical square, together with the main theorem's
counit clause; it does not unfold its construction. Its signature and value stay identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | M7 | Three definitionally equal bodies and one public import; signatures preserved. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | unclaimed | Three derived-comparison references, no H⁰ references; same signature and value, no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricPointPullbackTensorNormalization | unclaimed | None of these names occurs; no adaptation. |

Both original consumers compiled against the changed item without errors or warnings
(6.1 and 7.7 seconds); neither is included in the delivery.

The target statements are unchanged. Their meaning is unchanged because the new named
constructions unfold to the old composites. The independent review checks these definition
changes and the affected target meanings as required by stage 2 §4.

## Status

landed 20261020T211801-L-3501671 2026-10-20 (merge of deliver/M7/Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction)
