# ModuleCat.exists_localizedTensorComparison_direct_sum_square

## Reason

Retire the duplicate listed in coord/retire-items.tsv, as authorized by
coord/changes/retire-sheaf-twins-20261020.md. The adopted source theorem already
proves the same square without the unused hC, hQ, and hU assumptions. The current
Sheaf item has zero holes. No upstream file is changed.

## Old

The duplicate's signature, under the original ring, derived-category, Q, N and t
section variables, is:

```lean
theorem exists_localizedTensorComparison_direct_sum_square
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    {I : Type u} (U : I → CochainComplex (ModuleCat.{u} A) ℤ)
    (hU : ∀ j (V : CochainComplex (ModuleCat.{u} A) ℤ), V.Acyclic →
      (CochainComplex.mapBifunctor V (U j) (curriedTensor _)).Acyclic)
    (m : ∀ j, BaseDerivedTensorCohomologyModel R A B (U j ⊗ Q) C)
    (mS : BaseDerivedTensorCohomologyModel R A B ((∐ U) ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let α := fun j ↦ (m j).localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F (U j) Q).inv ≫ (F.obj (U j) ◁ t)) i
    ∃ (e : (∐ fun j ↦ (extendScalars (algebraMap (A ⊗[R] B) C)).obj
        ((m j).cohomology i)) ≅
      (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mS.cohomology i))
      (d : (∐ fun j ↦ (F.obj (U j) ⊗ N).homology i) ≅
        (F.obj (∐ U) ⊗ N).homology i),
      Limits.Sigma.map α ≫ d.hom = e.hom ≫
        (mS.localizedComparison i ≫ HomologicalComplex.homologyMap
          ((Functor.Monoidal.μIso F (∐ U) Q).inv ≫ (F.obj (∐ U) ◁ t)) i)
```

## New

The unchanged adopted source theorem, with the same section variables, is:

```lean
theorem exists_localizedTensorComparison_direct_sum_square
    {I : Type u} (U : I → CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ∀ j, BaseDerivedTensorCohomologyModel R A B (U j ⊗ Q) C)
    (mS : BaseDerivedTensorCohomologyModel R A B ((∐ U) ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let α := fun j ↦ (m j).localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F (U j) Q).inv ≫ (F.obj (U j) ◁ t)) i
    ∃ (e : (∐ fun j ↦ (extendScalars (algebraMap (A ⊗[R] B) C)).obj
        ((m j).cohomology i)) ≅
      (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mS.cohomology i))
      (d : (∐ fun j ↦ (F.obj (U j) ⊗ N).homology i) ≅
        (F.obj (∐ U) ⊗ N).homology i),
      Limits.Sigma.map α ≫ d.hom = e.hom ≫
        (mS.localizedComparison i ≫ HomologicalComplex.homologyMap
          ((Functor.Monoidal.μIso F (∐ U) Q).inv ≫ (F.obj (∐ U) ◁ t)) i)
```

The Sheaf file is withdrawn via deleted.txt. Its node now attaches to the
adopted source module and records the exact stronger signature; the mathematical
node statement is unchanged and follows by ignoring its extra hypotheses.
The existing source proof and its source-coproduct and homology dependencies
remain intact. Empty and arbitrary infinite families remain included.

## Users

`tools/downstream.py` with `--uses exists_localizedTensorComparison_direct_sum_square`
finds one downstream module and one application. A search of quarantine finds
no additional consumer. The sole DAG parent retains the same dependency node,
whose attachment now resolves to the adopted source theorem.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.LocalizedTensorComparisonDirectSumSquare | C5 | Withdraw duplicate; attach node to source theorem. |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct | unclaimed | Switch proof import to source and omit hC, hQ, hU from the direct-sum-square application. Keep all declaration signatures and public imports. Scope the unused-variable linter off for the first closure theorem because its retained hC premise is no longer needed by its proof. |

## Status

landed 20261020T235546-L-1189300 2026-10-20 (merge of deliver/C5/Sheaf.Algebra.Homology.LocalizedTensorComparisonDirectSumSquare)
