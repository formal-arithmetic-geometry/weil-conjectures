# ModuleCat.exists_localizedTensorComparison_cone_rows

## Reason

The queue assigns retirement of the zero-hole Sheaf copy. The adopted source
contains a proved theorem with the same name and conclusion, omitting the three
unneeded K-flatness hypotheses hQ, hK₁ and hK₂. Its proof is otherwise the same
cone-triangle, naturality and boundary argument. The full former Sheaf signature
is proved by a direct application in scratchpad/Compatibility.lean.

## Old

The Sheaf module declared the following theorem under the ring, derived-category,
Q, N and coefficient-map variables listed unchanged in both modules:

```lean
theorem exists_localizedTensorComparison_cone_rows
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (P₁ P₂ : CochainComplex (ModuleCat.{u} A) ℤ) (f : P₁ ⟶ P₂)
    (hK₁ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V P₁ (curriedTensor _)).Acyclic)
    (hK₂ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V P₂ (curriedTensor _)).Acyclic)
    (m₁ : BaseDerivedTensorCohomologyModel R A B (P₁ ⊗ Q) C)
    (m₂ : BaseDerivedTensorCohomologyModel R A B (P₂ ⊗ Q) C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B (CochainComplex.mappingCone f ⊗ Q) C)
    (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let E := extendScalars (algebraMap (A ⊗[R] B) C)
    let P₃ := CochainComplex.mappingCone f
    let cmp := fun (V : CochainComplex (ModuleCat.{u} A) ℤ)
      (m : BaseDerivedTensorCohomologyModel R A B (V ⊗ Q) C) (j : ℤ) ↦
        m.localizedComparison j ≫ HomologicalComplex.homologyMap
          ((Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)) j
    let d₀ := HomologicalComplex.homologyMap (F.map f ▷ N) i
    let d₁ := HomologicalComplex.homologyMap (F.map (CochainComplex.mappingCone.inr f) ▷ N) i
    let d₂ := CochainComplex.homologyδOfTriangle
      (tensorConeTriangle
        ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B))) f N) i (i + 1)
    let d₃ := HomologicalComplex.homologyMap (F.map f ▷ N) (i + 1)
    ∃ (s₀ : E.obj (m₁.cohomology i) ⟶ E.obj (m₂.cohomology i))
      (s₁ : E.obj (m₂.cohomology i) ⟶ E.obj (m₃.cohomology i))
      (s₂ : E.obj (m₃.cohomology i) ⟶ E.obj (m₁.cohomology (i + 1)))
      (s₃ : E.obj (m₁.cohomology (i + 1)) ⟶ E.obj (m₂.cohomology (i + 1))),
      (ComposableArrows.mk₄ s₀ s₁ s₂ s₃).Exact ∧
      s₀ ≫ cmp P₂ m₂ i = cmp P₁ m₁ i ≫ d₀ ∧
      s₁ ≫ cmp P₃ m₃ i = cmp P₂ m₂ i ≫ d₁ ∧
      s₂ ≫ cmp P₁ m₁ (i + 1) = cmp P₃ m₃ i ≫ d₂ ∧
      s₃ ≫ cmp P₂ m₂ (i + 1) = cmp P₁ m₁ (i + 1) ≫ d₃
```

## New

Retire lean/Sheaf/Algebra/Homology/LocalizedTensorComparisonConeRows.lean via
deleted.txt. Reattach its existing DAG node to the preserved source theorem:

```lean
theorem exists_localizedTensorComparison_cone_rows
    (hC : Module.Flat (A ⊗[R] B) C)
    (P₁ P₂ : CochainComplex (ModuleCat.{u} A) ℤ) (f : P₁ ⟶ P₂)
    (m₁ : BaseDerivedTensorCohomologyModel R A B (P₁ ⊗ Q) C)
    (m₂ : BaseDerivedTensorCohomologyModel R A B (P₂ ⊗ Q) C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B (CochainComplex.mappingCone f ⊗ Q) C)
    (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let E := extendScalars (algebraMap (A ⊗[R] B) C)
    let P₃ := CochainComplex.mappingCone f
    let cmp := fun (V : CochainComplex (ModuleCat.{u} A) ℤ)
      (m : BaseDerivedTensorCohomologyModel R A B (V ⊗ Q) C) (j : ℤ) ↦
        m.localizedComparison j ≫ HomologicalComplex.homologyMap
          ((Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)) j
    let d₀ := HomologicalComplex.homologyMap (F.map f ▷ N) i
    let d₁ := HomologicalComplex.homologyMap (F.map (CochainComplex.mappingCone.inr f) ▷ N) i
    let d₂ := CochainComplex.homologyδOfTriangle
      (tensorConeTriangle
        ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B))) f N) i (i + 1)
    let d₃ := HomologicalComplex.homologyMap (F.map f ▷ N) (i + 1)
    ∃ (s₀ : E.obj (m₁.cohomology i) ⟶ E.obj (m₂.cohomology i))
      (s₁ : E.obj (m₂.cohomology i) ⟶ E.obj (m₃.cohomology i))
      (s₂ : E.obj (m₃.cohomology i) ⟶ E.obj (m₁.cohomology (i + 1)))
      (s₃ : E.obj (m₁.cohomology (i + 1)) ⟶ E.obj (m₂.cohomology (i + 1))),
      (ComposableArrows.mk₄ s₀ s₁ s₂ s₃).Exact ∧
      s₀ ≫ cmp P₂ m₂ i = cmp P₁ m₁ i ≫ d₀ ∧
      s₁ ≫ cmp P₃ m₃ i = cmp P₂ m₂ i ≫ d₁ ∧
      s₂ ≫ cmp P₁ m₁ (i + 1) = cmp P₃ m₃ i ≫ d₂ ∧
      s₃ ≫ cmp P₂ m₂ (i + 1) = cmp P₁ m₁ (i + 1) ≫ d₃
```

The mathematical node statement retains its hypotheses; the stronger source
statement proves it by specialization. The node's proof and proof dependencies
still describe the preserved source proof. No upstream file, target statement,
definition, unit route, or parent dependency changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonConeRows | C9 | Retired duplicate. |
| WeilConjectures.Algebra.Homology.LocalizedTensorComparisonTriangleFiveTermDiagram | unclaimed | Already imports and applies the source theorem without the dropped hypotheses; unchanged; profiled compile passed in 51.8 seconds; former-signature compatibility also compiled. |

The downstream.py query reports zero current importers of the Sheaf copy.
Whole-library and quarantine searches confirm this. The retirement table's old
consumer Sheaf.Algebra.Homology.LocalizedTensorComparisonTriangleFiveTermDiagram
is already absent; its node points to the source counterpart, whose proof uses
this same source theorem. Parent DAG dependencies on the cone-row node remain
valid through its updated Lean attachment. No node is deleted, and the unit
sk-thm-picard-semicon has no realized attachment to this module. There are no
forced consumer adaptations.

## Status

landed 20261020T233113-L-893834 2026-10-20 (merge of deliver/C9/Sheaf.Algebra.Homology.LocalizedTensorComparisonConeRows)
