# Remove duplicate equivariant module sheaf declaration

## Reason

Upstream review #1428 identified two copy-pasted declarations with the same fully qualified name. The restricted-scalars proposition is the one used by downstream callers. Its single implementation is retained in the assigned `TorsorEquivariantModuleIsSheaf` module. The companion interface claim is explicit because its duplicate-removal change is intentional.

## Old

`TorsorEquivariantModuleIsSheaf` declared:

```lean
theorem Scheme.GaloisCover.equivariantModulePresheaf_isSheaf
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (N : Rep.{u + 1} (ZMod ℓ) P) :
    Presheaf.IsSheaf V.smallEtaleTopology (c.equivariantModulePresheaf ℓ N)
```

`TorsorEquivariantPresheafSheaf` also declared the same fully qualified name with the restricted-scalars signature:

```lean
theorem Scheme.GaloisCover.equivariantModulePresheaf_isSheaf
    {V : Scheme.{u}} (ℓ : ℕ) (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) (N : Rep.{u + 1} (ZMod ℓ) P) :
    Presheaf.IsSheaf V.smallEtaleTopology
      (c.equivariantModulePresheaf ℓ N ⋙ ModuleCat.restrictScalars
        (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ))
```

## New

`TorsorEquivariantModuleIsSheaf` retains the restricted-scalars declaration with the complete signature:

```lean
theorem Scheme.GaloisCover.equivariantModulePresheaf_isSheaf
    {V : Scheme.{u}} (ℓ : ℕ) (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) (N : Rep.{u + 1} (ZMod ℓ) P) :
    Presheaf.IsSheaf V.smallEtaleTopology
      (c.equivariantModulePresheaf ℓ N ⋙ ModuleCat.restrictScalars
        (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ))
```

`TorsorEquivariantPresheafSheaf` removes its duplicate declaration and private implementation, and publicly imports `Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf`. The complete retained signature above remains available to its callers. Both modules are explicitly claimed by R4; the companion edit is an intentional interface change, not a forced adaptation. No definition or target statement changes. The two sheaf propositions are equivalent under restriction along the ring equivalence, and the retained proposition is the one required by the companion callers.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull | unclaimed | Its sheaf proof is adapted to call the retained theorem with explicit `P`; this is the required forced proof adaptation. |
| Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf | R4 | Explicitly claimed compatibility module: replace duplicate implementation by public import of the retained theorem; callers keep the same restricted-scalars signature. |
| Sheaf.ConstructibleSheaf.TorsorInvariantSections | unclaimed | Existing theorem reference remains valid. |
| Sheaf.ConstructibleSheaf.TorsorSectionEvaluationBijective | unclaimed | Existing theorem reference remains valid. |

## Status

landed 20261013T222412-L-1226410 2026-10-13 (merge of deliver/R4/Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf)
