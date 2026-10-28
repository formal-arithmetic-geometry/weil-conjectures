# WeilConjectures.IntegralHom.tensor_presentation_evaluation

## Reason

The earlier statement quantifies over every adjunction between the fixed tensor
and Hom functors, yet requires its counit to agree with a fixed signed chain
evaluation. This is false: twisting a right adjoint by the natural automorphism
minus identity negates the counit while leaving the two functors unchanged.
On complexes concentrated in degree zero with rank-one integral coefficients
(for example at l=3), the section formula fixes beta to multiplication. The
oppositely normalized counit would require its nonzero localization to be negative
multiplication. Thus the missing normalization cannot be deduced for arbitrary adj.

The source (current blueprint integral-Hom reduction proof, paragraph 2, Stacks
08J9 and 06YU) uses the actual evaluation adjunction. Construct a family of
adjunctions simultaneously with its evaluation normalization, transporting the
recorded right-tensor adjunction by the normalized Koszul exchange.

This corrects an intermediate theorem, not a target. The same TensorPresentation
existence statement is proved by the adapted caller. No coefficient definition,
TensorPresentation field, target signature, existing public import, or source-library
declaration changes.

## Old

```lean
theorem tensor_presentation_evaluation
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheaf l E Y D hl)))
    (T : CoefficientTensorModels (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheaf l E Y D hl) S)
    (adj : ∀ K : Derived.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl),
      (Functor.curry.obj S.tensor).obj K ⊣
        (Functor.curry.obj (hom Y
          (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)) :
    ∀ (P I S' : CochainComplex (Modules.{t,u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) ℤ)
      (hP : flat.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) P)
      (hS : flat.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) S'), I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{t+1,t,max u (t+1),max u (t+1)}
        (R := completedIntegralCommRingSheaf l E Y D hl) P I,
      ∃ beta : ((totalTensor.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj S' ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S'.X j).val.obj U),
          (beta.f (i+j)).val.app U
            (totalPair.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) P S' i j U x s) =
            (i*j).negOnePow • evaluate.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl)
              P I j i U ((q.f j).val.app U s) x) ∧
        T.comparison.inv.app (⟨P,hP⟩,⟨S',hS⟩) ≫ DerivedCategory.Q.map beta =
          S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫ homModelMap.{t,u} Y
              (completedIntegralCommRingSheaf l E Y D hl) P I)) ≫
          (adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I)
```

## New

```lean
theorem tensor_presentation_evaluation
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheaf l E Y D hl)))
    (T : CoefficientTensorModels (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheaf l E Y D hl) S)
    : ∃ adj : ∀ K : Derived.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl),
      (Functor.curry.obj S.tensor).obj K ⊣
        (Functor.curry.obj (hom Y
          (completedIntegralCommRingSheaf l E Y D hl))).obj (op K),
    ∀ (P I S' : CochainComplex (Modules.{t,u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) ℤ)
      (hP : flat.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) P)
      (hS : flat.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) S'), I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{t+1,t,max u (t+1),max u (t+1)}
        (R := completedIntegralCommRingSheaf l E Y D hl) P I,
      ∃ beta : ((totalTensor.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj S' ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S'.X j).val.obj U),
          (beta.f (i+j)).val.app U
            (totalPair.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) P S' i j U x s) =
            (i*j).negOnePow • evaluate.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl)
              P I j i U ((q.f j).val.app U s) x) ∧
        T.comparison.inv.app (⟨P,hP⟩,⟨S',hS⟩) ≫ DerivedCategory.Q.map beta =
          S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫ homModelMap.{t,u} Y
              (completedIntegralCommRingSheaf l E Y D hl) P I)) ≫
          (adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I)
```

## Users

`tools/downstream.py ... --uses tensor_presentation_evaluation` finds exactly the
two declarations below (including the defining module). The sole direct importer
is IntegralHomTensorPresentation. Other transitive importers do not mention the
changed name, and the constructor's exported signature is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralHomTensorPresentationEvaluation | S4 | Construct normalized adj and prove its formula and comparison; zero sorry. |
| Sheaf.Paper.IntegralHomTensorPresentation | unclaimed (server checked 2026-10-28) | Obtain adj and its evaluation field together. Remove the obsolete adjunction proof import; exported theorem unchanged. |
| Sheaf.Paper.IntegralHomEvaluationCoefficient | S4 (new module) | Fully proved equality of the existing evaluation notations, isolated for compile time; no holes. |

The old adjunction-only module is held by J4 and is untouched. Its only consumer
was the constructor; this delivery removes that consumer's import and DAG edge.
It is reported for pruning rather than deleted or modified.

## Status

landed 20261028T055753-L-806781 2026-10-28 (merge of deliver/S4/Sheaf.Paper.IntegralHomTensorPresentationEvaluation)
