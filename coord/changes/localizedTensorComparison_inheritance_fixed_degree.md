# ModuleCat.localizedTensorComparison_inheritance_fixed_degree

## Reason
The old single-degree premise is false. Let R=A=B=C=Z, Q=0, N the complex Z
concentrated in degree 1, U the complex Z concentrated in degree -1, and i=0.
The canonical E=Z tensor_Z Z to Z is an isomorphism, so C is flat over E.
U and Q are K-flat. Both base-derived cohomology models have zero cohomology
because Q=U tensor Q=0. The old premise is 0 to H^0(N)=0, an isomorphism.
The conclusion is 0 to H^0(U tensor N)=Z, which is not an isomorphism.

The source Tag 0DJA(1) assumes the full base-change condition; the global
caller already has comparison isomorphisms in every degree. The corrected
helper therefore retains a fixed-degree conclusion and requires its premise
in all degrees. No Challenge target changes. The new proof is a decomposition
of the corrected assertion, not a proof of the false old assertion.

## Old
```lean
theorem localizedTensorComparison_inheritance_fixed_degree
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    (hC : Module.Flat (A ⊗[R] B) C)
    (U Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} C) ℤ)
    (hU : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} B)
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∀ (t : F.obj Q ⟶ N)
      (m : BaseDerivedTensorCohomologyModel R A B Q C)
      (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C)
      (i : ℤ),
      (IsIso (m.localizedComparison i ≫ HomologicalComplex.homologyMap t i)) →
      IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i)
```

## New
```lean
theorem localizedTensorComparison_inheritance_fixed_degree
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    (hC : Module.Flat (A ⊗[R] B) C)
    (U Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} C) ℤ)
    (hU : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} B)
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∀ (t : F.obj Q ⟶ N)
      (m : BaseDerivedTensorCohomologyModel R A B Q C)
      (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C)
      (i : ℤ),
      (∀ j : ℤ, IsIso (m.localizedComparison j ≫ HomologicalComplex.homologyMap t j)) →
      IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i)
```
Two redundant direct public imports are removed from the helper: Mathlib.Algebra.Homology.Monoidal and WeilConjectures.Mathlib.Algebra.Homology.Bifunctor. Both remain publicly available through the retained public imports, so the exported declarations are preserved. The new generator and closure modules import their planned mixed-ring associator privately.

The explicit comparison predicate has no postponed data. The generator and
closure statements are the two remaining proof obligations. The existing
free-generation theorem combines them.

## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritance | unclaimed | Forced proof-only adaptation: pass h instead of h i. Its statement and visibility are identical. |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritanceFixedDegree | G2 | Corrected intermediate statement and completed reduction. |

The downstream source scan finds no other use of the changed declaration.
All 423 transitive importers retain their statements: the sole direct caller
retains its interface, so its clients need no adaptation. None of the five
Challenge declarations changes its signature or the definitions it uses.

## Status
landed 20261013T165640-L-1807630 2026-10-13 (merge of deliver/G2/Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritanceFixedDegree)
