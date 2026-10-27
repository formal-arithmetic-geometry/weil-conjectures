# totalComparison_existsUnique

## Reason

Repeatedly elaborating the full equivalence functor inside the total-complex types
is expensive. Bind that same functor and its induced complex functor once by local lets. Zeta reduction and proof irrelevance
give exactly the original statement, with the same hypotheses, tensor
products, summand inclusions and normalization. This adds no mathematical hypothesis
and changes no map. The body of totalComparison remains the same unique choice.
Explicit existing total-existence proofs and local transparency settings avoid
repeated instance searches without changing public data. These local proof bindings
add no hypothesis. Their class arguments are propositions, so proof irrelevance
identifies their choices with the original ones.

## Old

```lean
theorem totalComparison_existsUnique (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    ∃! t : ((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor _)) ≅
      CochainComplex.mapBifunctor
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
        (curriedTensor _),
    ∀ (p q n : ℤ) (h : p + q = n),
      (equivalence Λ X).functor.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫ t.hom.f n =
        (ordinaryTensorComparison Λ X (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
            (curriedTensor _) p q n h
```

## New

```lean
theorem totalComparison_existsUnique (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    let F := (equivalence Λ X).functor
    let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
    have : CochainComplex.HasMapBifunctor P Q (curriedTensor (internalModules Λ X)) :=
      @InternalAbelianSheafModule.comparison_internalTotalExists
        X.ProEt _ (Scheme.ProEt.topology X) _ _ _ (condensedRingObj Λ X) _
        (isCommMonObj_condensedRingObj Λ X) P Q
    have : CochainComplex.HasMapBifunctor (G.obj P) (G.obj Q)
        (curriedTensor (modules Λ X)) := fun _n ↦
      ((inferInstance : HasColimitsOfSize.{0, 0}
        (modules Λ X)).has_colimits_of_shape _).has_colimit _
    ∃! t : G.obj
        (CochainComplex.mapBifunctor P Q (curriedTensor _)) ≅
      CochainComplex.mapBifunctor
        (G.obj P)
        (G.obj Q)
        (curriedTensor _),
    ∀ (p q n : ℤ) (h : p + q = n),
      F.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫ t.hom.f n =
        (ordinaryTensorComparison Λ X (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor
            (G.obj P)
            (G.obj Q)
            (curriedTensor _) p q n h
```

## Users

The table includes the results for totalComparison_existsUnique (the item only)
and totalComparison. The latter declaration's source body and inferred isomorphism
type are unchanged after zeta reduction. No consumer source or signature needs
adaptation; no held module is edited. All targets and their mathematical meanings
are unchanged. The separate PushNormalized representation change is recorded in
K9-section-push-normalization.md and is submitted for semantic review there.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | K9 | The theorem uses local functor aliases and explicit total-existence proofs; the totalComparison choice body is unchanged. |
| Sheaf.Paper.SectionDerivedRealization | R1 | Only an irreducibility attribute uses totalComparison; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | The same comparison morphism is mapped by Q; no adaptation. |
| Sheaf.Paper.SectionKFlatTensorComparison | unclaimed | Only an irreducibility attribute; no adaptation. |
| Sheaf.Paper.SectionResolutionConjugationIdentities | unclaimed | The same totalComparison.hom is mapped; no adaptation. |
| Sheaf.Paper.SectionResolvingOplaxConstraintDiagrams | unclaimed | Only an irreducibility attribute; no adaptation. |
| Sheaf.Paper.SectionTotalOplaxComparisonData | unclaimed | The same comparison iso and compositions; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Text hit refers to an unrelated totalComparison field; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed | Text hit refers to an unrelated totalComparison field; no adaptation. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed | Text hit refers to an unrelated totalComparison field; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientCochains | unclaimed | Text hit refers to an unrelated totalComparison field; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientData | unclaimed | Text hit refers to an unrelated totalComparison field; no adaptation. |

## Status

landed 20261026T070233-L-3486174 2026-10-26 (merge of deliver/K9/Sheaf.Paper.ProEtaleSectionModuleFunctors)
