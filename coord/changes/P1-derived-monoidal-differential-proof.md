# AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorComplexHom_comm

## Reason

Fill the original differential-compatibility hole without changing any statement or
construction. A proved private helper checks the equality after each tensor-summand
inclusion. The total differential formula, tensorator naturality and additivity prove
its two terms. This is the elementary chain-map argument already specified by proof
step 4 of `new-proetale-derived-module-pullback-monoidal`.

Private proof imports and proved proposition caches make the existing module-category
instances available within the compiler limit. Explicit arguments in `leftDerivedUpperStarTensor_fac` avoid repeated inference. Synchronous elaboration retains full kernel checking.
Existing public imports, signatures, attributes and non-holed construction data stay
verbatim. No other module is adapted; no definition or target changes meaning.

## Old

```lean
lemma upperStarTensorComplexHom_comm
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n n' : ℤ)
    (_ : (ComplexShape.up ℤ).Rel n n') :
    upperStarTensorComplexHomX Λ f A B n ≫
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).d n n' =
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).d n n' ≫
        upperStarTensorComplexHomX Λ f A B n' :=
  sorry
```

## New

```lean
lemma upperStarTensorComplexHom_comm
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n n' : ℤ)
    (_ : (ComplexShape.up ℤ).Rel n n') :
    upperStarTensorComplexHomX Λ f A B n ≫
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).d n n' =
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).d n n' ≫
        upperStarTensorComplexHomX Λ f A B n' :=
  by
  refine (f)^*⟦Λ⟧.privateTensorDesc_comm A B (upperStarTensorComplexHomX Λ f A B) ?_ n n' ‹_›
  intro p q k h
  rw [upperStarTensorComplexHomX, HomologicalComplex.ι_mapBifunctorDesc]
```

## Users

The source-only downstream search for `upperStarTensorComplexHom_comm` finds only
the assigned module; its construction continues to call the identical theorem.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal | P1 | One theorem proof filled; public interface and construction data preserved. |

The returned delivery at c0005dcbb65 added local priority attributes after two existing
holed instances. This repair removes both attributes and preserves each original instance
block verbatim. The source-only hole gate consequently reports no changed holed instance.

## Status

landed 20261022T025337-L-1287772 2026-10-22 (merge of deliver/P1/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal)
