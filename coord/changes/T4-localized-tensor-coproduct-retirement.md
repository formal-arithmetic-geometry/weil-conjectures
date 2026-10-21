# ModuleCat.localizedTensorComparisonProperty_closure_coproducts

## Reason

Complete the retirement assigned by coord/retire-items.tsv, row 1519, under the
human authorization in coord/changes/retire-sheaf-twins-20261020.md. Both
declarations already have complete proofs. The adopted source twin proves the
same conclusions without the unused hC premise. No upstream file is changed.

## Old

Under the unchanged ring, algebra, derived-category, Q, N and t section variables:

```lean
theorem localizedTensorComparisonProperty_closure_coproducts
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    ∀ {I : Type u} (G : I → DerivedCategory (ModuleCat.{u} A))
      (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, G i ⟶ S),
      CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk S ι) →
      (∀ i, localizedTensorComparisonProperty R A B C Q N t (G i)) →
      localizedTensorComparisonProperty R A B C Q N t S
```

```lean
theorem localizedTensorComparisonProperty_closure_coproducts_fixed_degree
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    {I : Type u} (G : I → DerivedCategory (ModuleCat.{u} A))
    (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, G i ⟶ S)
    (hc : CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk S ι))
    (hs : ∀ i, localizedTensorComparisonProperty R A B C Q N t (G i))
    (U : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : Nonempty (DerivedCategory.Q.obj U ≅ S))
    (hU : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i)
```

## New

The Sheaf module is withdrawn. Both nodes attach to the existing adopted source
module WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct,
with these verbatim signatures under the same section variables:

```lean
theorem localizedTensorComparisonProperty_closure_coproducts
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    ∀ {I : Type u} (G : I → DerivedCategory (ModuleCat.{u} A))
      (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, G i ⟶ S),
      CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk S ι) →
      (∀ i, localizedTensorComparisonProperty R A B C Q N t (G i)) →
      localizedTensorComparisonProperty R A B C Q N t S
```

```lean
theorem localizedTensorComparisonProperty_closure_coproducts_fixed_degree
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    {I : Type u} (G : I → DerivedCategory (ModuleCat.{u} A))
    (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, G i ⟶ S)
    (hc : CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk S ι))
    (hs : ∀ i, localizedTensorComparisonProperty R A B C Q N t (G i))
    (U : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : Nonempty (DerivedCategory.Q.obj U ≅ S))
    (hU : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i)
```

The mathematical node statements, proof steps, and dependencies are unchanged.
The original statements follow by ignoring their extra hC assumption. The source
proof uses precisely the original coproduct and representative-square argument.

## Users

Current downstream scans and searches of Lean and quarantine find no importer of
the Sheaf module and no external application to its declarations. The former
consumer already uses the official twin. The DAG parent still cites the same node;
its attachment now resolves to the existing theorem, so no dependency is removed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct | T4 | Withdraw duplicate and reattach both nodes. |
| WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosure | unclaimed | Already imports the official twin and applies its API without hC; unchanged. |

## Status

landed 20261021T002151-L-1494865 2026-10-21 (merge of deliver/T4/Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct)
