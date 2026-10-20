# AlgebraicGeometry.exists_tensorHomUncurry_descent_representative

## Reason

Restore the assigned quarantined module after upstream sync 5f7b33eac. The archived
module refers to `IsAcyclicTensorKFlat`, which is unavailable through its current imports.
The adopted source already proves the same fully qualified theorem with the canonical
`CochainComplex.IsKFlatTensor` predicate. Its definition body in
`WeilConjectures.Algebra.Homology.KFlat` is identical to `IsAcyclicTensorKFlat` in
`Sheaf.Algebra.Homology.KFlat`: tensoring an arbitrary acyclic complex with the given
complex yields an acyclic total tensor complex.

Restore the original Sheaf path as a public re-export of the upstream theorem. This
provides the missing interface without declaring the same constant twice. The node
keeps its existing Sheaf module/file attachment, statement dependencies, proof steps,
and representative-coherence proof dependency. Its recorded Lean signature uses the
current predicate name. There is no withdrawal, no target change, and no source-library
edit. The theorem is already proved, and its printed axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Old

```lean
theorem exists_tensorHomUncurry_descent_representative (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := schemeDerivedTensorMonoidal X
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsAcyclicTensorKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M
```

## New

Publicly re-exported from
`WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative`:

```lean
theorem exists_tensorHomUncurry_descent_representative (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := schemeDerivedTensorMonoidal X
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative | N3 assignment | Restore the module as a re-export of the canonical proved theorem. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescent | unclaimed; quarantined | Sole archived direct importer and caller. The mathematical premise and conclusion agree. Its independent obsolete K-flat references remain for its own rework assignment; no change here. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescent | unclaimed | Uses the upstream theorem already. Its signature and proof stay unchanged. |

`tools/downstream.py --allow-missing --uses` reports no live downstream modules for
the absent Sheaf path. Searches in both `lean/` and `quarantine/` additionally locate
the archived direct importer and the upstream caller listed above. The DAG parent
`lem-pc-tensor-hom-uncurry-descent` still cites this node, so its Lean attachment and
all mathematical dependencies are preserved. No consumer adaptation is required.
The restored module compiles, including explicit theorem-visibility and axiom probes.

## Status

landed 20261020T161735-L-3529914 2026-10-20 (merge of deliver/N3/Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative)
