# AlgebraicGeometry.Etale.constantDerivedProjectionMap

## Reason

The original component definition makes the kernel unfold large concrete derived tensor instances when applying the generic generator proof. Full checks exceeded 60 seconds even though elaboration completed. Package explicit components, their reflexive identification with the specified transformation, and transfer of pointwise invertibility once. This shares the instance arguments and preserves the canonical mate definitionally. No object is selected from an existence theorem. The component is still `(τ.app E).app K`; its equality field and invertibility transport are proved. No target or existing signature changes.

## Old

```lean
noncomputable def constantDerivedProjectionMap (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory A) :
    (((rightDerivedGlobalSections A X) ⋙
      curriedTensor (DerivedCategory A)).obj E).obj K ⟶
    (((Functor.postcompose₂.obj (rightDerivedGlobalSections A X)).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor).obj
          (curriedTensor _))).obj E).obj K :=
  (((derivedConstantGlobalSectionsAdjunction A X).rightAdjointProjectionMap
    (constantSheaf X.smallEtaleTopology A).leftDerivedTensorComparison).app
      E).app K
```

## New

```lean
noncomputable def constantDerivedProjectionMap (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory A) :
    (((rightDerivedGlobalSections A X) ⋙
      curriedTensor (DerivedCategory A)).obj E).obj K ⟶
    (((Functor.postcompose₂.obj (rightDerivedGlobalSections A X)).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor).obj
          (curriedTensor _))).obj E).obj K :=
  (constantProjectionComponents A X).component E K
```

The explicit `ProjectionComponents` structure, `projectionComponents` constructor and `constantProjectionComponents` specialization precede this definition in the same module. All data are defined and all proof fields are proved. The existing source docstrings and C6 proofs are retained. A target using this definition has unchanged mathematical meaning; definition review is requested with this record.

## Users

`tools/downstream.py --uses` reports the following direct name users (the map has four, the adjunction six, including its defining module). There are 233 transitive downstream modules; no signature or instance changes propagate to them.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap | unclaimed | Definitionally equal component interface; no signature change. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula | Q8 | Proof of original statement supplied in this delivery. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow | D2 | Unchanged original compiles against repair. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | P5 | Unchanged original compiles against repair. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | W4 | Unchanged original compiles against repair. |
| Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing | A7 | Unchanged original compiles against repair. |
| Sheaf.Paper.ExternalRHomConePairing | F2 | Original fails with duplicate HomComplex import both with and without sandbox repair; unchanged baseline failure. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Unchanged original compiles against repair. |

The five independent consumers passed at 20.0, 44.4, 19.3, 35.8 and 37.2 seconds. ExternalRHomConePairing fails during imports because upstream and Sheaf HomComplex modules both declare CategoryTheory.homComplexFunctor. The original copied outside the sandbox module overlay fails identically, before any use of this definition. No consumer adaptation is needed or delivered.

## Status

landed 20261020T132030-L-1404354 2026-10-20 (merge of deliver/Q8/Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula)
