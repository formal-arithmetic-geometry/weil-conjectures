# CategoryTheory.Sheaf.compact_cech_intersections

## Reason

Repair return of U6 item `Sheaf.Topology.QuasiCompactRestrictionAcyclicity`
(head `620927ceb45`): its duplicate private helper must be replaced by reuse of
this existing theorem. It was private and therefore inaccessible to importers.
Expose the existing theorem in its original module, preserving its binders,
conclusion, and complete proof. Add a short docstring. No definition changes.

## Old

```lean
private theorem compact_cech_intersections
    {X : Type u} [TopologicalSpace X]
    (hpairs : ∀ U V : TopologicalSpace.Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : TopologicalSpace.Opens X) : Set X))
    {T : Type u} {U : TopologicalSpace.Opens X}
    {f : T → TopologicalSpace.Opens X} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom)
    (hc : ∀ t, IsCompact ((f t : TopologicalSpace.Opens X) : Set X)) :
    ∀ (p : ℕ) (a : Fin (p + 1) → T),
      IsCompact ((S.W p a : TopologicalSpace.Opens X) : Set X)
```

## New

```lean
theorem compact_cech_intersections
    {X : Type u} [TopologicalSpace X]
    (hpairs : ∀ U V : TopologicalSpace.Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : TopologicalSpace.Opens X) : Set X))
    {T : Type u} {U : TopologicalSpace.Opens X}
    {f : T → TopologicalSpace.Opens X} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom)
    (hc : ∀ t, IsCompact ((f t : TopologicalSpace.Opens X) : Set X)) :
    ∀ (p : ℕ) (a : Fin (p + 1) → T),
      IsCompact ((S.W p a : TopologicalSpace.Opens X) : Set X)
```

Both declarations remain in namespace `CategoryTheory.Sheaf` of
`Sheaf.Topology.FilteredInjectiveCechAcyclic`; only visibility changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.FilteredInjectiveCechAcyclic | unclaimed | Existing internal calls and theorem proofs unchanged. |
| Sheaf.Topology.QuasiCompactRestrictionAcyclicity | U6 | Remove duplicate helper; import and call the existing theorem. |

`tools/downstream.py Sheaf.Topology.FilteredInjectiveCechAcyclic --uses compact_cech_intersections`
found only the defining module. The module had zero downstream importers before
this repair. The proposed proof import is cycle-free. No consumer statement or
target meaning changes; no forced adaptation of another group's module occurs.

## Status

landed 20261023T170210-L-2075080 2026-10-23 (merge of deliver/U6/Sheaf.Topology.QuasiCompactRestrictionAcyclicity)
