# AlgebraicGeometry.Scheme.exists_stratification_of_stratified_partition

## Reason

Retire the zero-hole duplicate listed in `coord/retire-items.tsv`. The complete module,
including the theorem statement and proof, is identical to its adopted-source twin after
the copyright header. The sole direct consumer can therefore use that twin unchanged.
The upstream proof and all of its imports remain verbatim. No definition, target, unit
route, mathematical statement, or proof dependency changes.

## Old

In `Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly`:

```lean
theorem exists_stratification_of_stratified_partition
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (Y : Fin n → Scheme.{u}) (ι : ∀ i, Y i ⟶ X)
    (hι : ∀ i, IsImmersion (ι i))
    (hc : ∀ i, Topology.IsConstructible (Set.range (ι i)))
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (ι i)) (Set.range (ι k))))
    (hu : (⋃ i, Set.range (ι i)) = Set.univ)
    (T : ∀ i, Stratification (Y i))
    (P : ∀ Z : Scheme.{u}, (Z ⟶ X) → Prop)
    (hP : ∀ i b, P ((T i).domain b) ((T i).immersion b ≫ ι i)) :
    ∃ R : Stratification X,
      (∀ k, Topology.IsConstructible (R.stratum k)) ∧
      ∀ k, P (R.domain k) (R.immersion k)
```

The consumer privately imports
`Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly`.

## New

The identical signature and complete proof already exist in
`WeilConjectures.AlgebraicGeometry.ConstructibleStratificationAssembly`:

```lean
theorem exists_stratification_of_stratified_partition
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (Y : Fin n → Scheme.{u}) (ι : ∀ i, Y i ⟶ X)
    (hι : ∀ i, IsImmersion (ι i))
    (hc : ∀ i, Topology.IsConstructible (Set.range (ι i)))
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (ι i)) (Set.range (ι k))))
    (hu : (⋃ i, Set.range (ι i)) = Set.univ)
    (T : ∀ i, Stratification (Y i))
    (P : ∀ Z : Scheme.{u}, (Z ⟶ X) → Prop)
    (hP : ∀ i b, P ((T i).domain b) ((T i).immersion b ≫ ι i)) :
    ∃ R : Stratification X,
      (∀ k, Topology.IsConstructible (R.stratum k)) ∧
      ∀ k, P (R.domain k) (R.immersion k)
```

The consumer privately imports that upstream module instead. The old Sheaf module is
withdrawn using `deleted.txt`; its node's `lean.module` and `lean.file` point to the
existing upstream theorem, retaining the declaration name and every other field.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly | Q1 | Retire duplicate; zero holes. |
| Sheaf.AlgebraicGeometry.ConstructibleExtFilteredColimit | unclaimed | Indirect consumer; identical theorem remains available; no source change. |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | unclaimed | Replace sole private import; all declarations, proof bodies, and public imports stay verbatim. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel | unclaimed | Indirect consumer; identical theorem remains available; no source change. |
| Sheaf.AlgebraicGeometry.NoetherianAffineFreePresentation | unclaimed | Indirect consumer; identical theorem remains available; no source change. |
| Sheaf.AlgebraicGeometry.NoetherianConstructibleGaloisPartition | unclaimed | Indirect consumer; identical theorem remains available; no source change. |
| Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel | unclaimed | Indirect consumer; identical theorem remains available; no source change. |
| Sheaf.AlgebraicGeometry.NoetherianEtaleSumConstructible | unclaimed | Indirect consumer; identical theorem remains available; no source change. |
| Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage | unclaimed | Indirect consumer; identical theorem remains available; no source change. |
| Sheaf.DeligneLaumon.NoetherianConstructibleFlatLifting | unclaimed | Indirect consumer; identical theorem remains available; no source change. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Indirect consumer; identical theorem remains available; no source change. |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | Indirect consumer; identical theorem remains available; no source change. |

The table contains every module reported by `tools/downstream.py` with `--uses`.
The only downstream textual use of the declaration is in `EtaleStratifiedFinite`.
Repository and quarantine searches find no additional direct importer or Lean use.
The two DAG references are the etale-stratified-finite parent's proof dependency and
proper-smooth-curves-prime-coefficients' approved tool-use record. Both remain valid:
the same assembly node and theorem are preserved upstream. The unit's realized nodes
are untouched. There are no signatures or definitions to adapt.

## Status

landed 20261020T160258-L-3350139 2026-10-20 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly)
