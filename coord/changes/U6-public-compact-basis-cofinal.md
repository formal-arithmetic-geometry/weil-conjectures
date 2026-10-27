# CategoryTheory.Sheaf.compact_basis_cofinal

## Reason

Repair return of U6 item `Sheaf.Topology.QuasiCompactRestrictionAcyclicity`
(head `620927ceb45`): its duplicate private helper must be replaced by reuse of
this existing theorem. It was private and therefore inaccessible to importers.
Expose the existing theorem in its original module, preserving its binders,
conclusion, and complete proof. Add a short docstring. No definition changes.

## Old

```lean
private theorem compact_basis_cofinal
    {X : Type u} [TopologicalSpace X]
    (hbasis : TopologicalSpace.Opens.IsBasis
      {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    (U : TopologicalSpace.Opens X) (hU : IsCompact (U : Set X))
    (T : Type u) (V : T → TopologicalSpace.Opens X) (f : ∀ t, V t ⟶ U)
    (hcover : Presieve.ofArrows V f ∈ (Opens.pretopology X).toPrecoverage U) :
    ∃ (K : Type u) (_ : Finite K) (W : K → TopologicalSpace.Opens X)
      (g : ∀ k, W k ⟶ U),
      (∀ k, IsCompact ((W k : TopologicalSpace.Opens X) : Set X)) ∧
      Presieve.ofArrows W g ∈ (Opens.pretopology X).toPrecoverage U ∧
      ∀ k, ∃ (t : T) (a : W k ⟶ V t), a ≫ f t = g k
```

## New

```lean
theorem compact_basis_cofinal
    {X : Type u} [TopologicalSpace X]
    (hbasis : TopologicalSpace.Opens.IsBasis
      {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    (U : TopologicalSpace.Opens X) (hU : IsCompact (U : Set X))
    (T : Type u) (V : T → TopologicalSpace.Opens X) (f : ∀ t, V t ⟶ U)
    (hcover : Presieve.ofArrows V f ∈ (Opens.pretopology X).toPrecoverage U) :
    ∃ (K : Type u) (_ : Finite K) (W : K → TopologicalSpace.Opens X)
      (g : ∀ k, W k ⟶ U),
      (∀ k, IsCompact ((W k : TopologicalSpace.Opens X) : Set X)) ∧
      Presieve.ofArrows W g ∈ (Opens.pretopology X).toPrecoverage U ∧
      ∀ k, ∃ (t : T) (a : W k ⟶ V t), a ≫ f t = g k
```

Both declarations remain in namespace `CategoryTheory.Sheaf` of
`Sheaf.Topology.FilteredInjectiveCechAcyclic`; only visibility changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.FilteredInjectiveCechAcyclic | unclaimed | Existing internal calls and theorem proofs unchanged. |
| Sheaf.Topology.QuasiCompactRestrictionAcyclicity | U6 | Remove duplicate helper; import and call the existing theorem. |

`tools/downstream.py Sheaf.Topology.FilteredInjectiveCechAcyclic --uses compact_basis_cofinal`
found only the defining module. The module had zero downstream importers before
this repair. The proposed proof import is cycle-free. No consumer statement or
target meaning changes; no forced adaptation of another group's module occurs.

## Status

landed 20261023T170210-L-2075080 2026-10-23 (merge of deliver/U6/Sheaf.Topology.QuasiCompactRestrictionAcyclicity)
