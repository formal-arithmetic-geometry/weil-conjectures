# AlgebraicGeometry.Scheme.exists_constructible_stratified_finite

## Reason

Retire the duplicate listed in coord/retire-items.tsv. The adopted source module
WeilConjectures.AlgebraicGeometry.ConstructibleStratifiedFinite already proves the exact
same theorem, including constructible strata, immersion data and finite pullbacks.
Both current proofs are complete; the upstream proof uses only propext, Classical.choice
and Quot.sound. No adopted-source file is edited.

## Old

The duplicate declaration was supplied by
Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite:

```lean
theorem exists_constructible_stratified_finite
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [Flat j] [LocallyOfFinitePresentation j] [IsSeparated j]
    (hj : j.IsQuasiFinite) :
    ∃ S : Stratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      (∀ i : Fin S.n, IsFinite (pullback.snd j (S.immersion i)))
```

Its private locally closed immersion helper is withdrawn with the duplicate module.

## New

The declaration with exactly the signature above is supplied by
WeilConjectures.AlgebraicGeometry.ConstructibleStratifiedFinite. The duplicate Sheaf
module is withdrawn through deleted.txt. Its only direct importer changes the private
proof import to the upstream module. The node's lean attachment follows that module;
its statement, proof steps and dependencies stay unchanged. The upstream proof realizes
all six steps of the existing plan, so no mathematical node or unit route is bypassed.
No target type or definition changes meaning.

## Users

The exact module/declaration scan of lean/ and quarantine/ finds only
Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite as a consumer of the withdrawn
module. Its proof and every declaration signature remain byte-identical; only its import
line changes. This is an unclaimed module at preparation time. tools/downstream.py
reports the following complete transitive downstream set. Only the direct importer
needs adaptation; private proof imports do not change its exposed interface.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite | R3 | Withdraw duplicate; node attaches to unchanged upstream theorem. |
| Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite | unclaimed | Private import redirected; theorem and proof unchanged; compiled. |
| Sheaf.AlgebraicGeometry.ConstructibleExtFilteredColimit | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.AlgebraicGeometry.NoetherianAffineFreePresentation | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.AlgebraicGeometry.NoetherianConstructibleGaloisPartition | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.AlgebraicGeometry.NoetherianEtaleSumConstructible | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.DeligneLaumon.NoetherianConstructibleFlatLifting | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Unchanged exposed interfaces; no edit. |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | Unchanged exposed interfaces; no edit. |

The only DAG parent is lem-weil-pbc-etale-separated-stratified-finite. Its existing
proof step still cites the same intermediate node, whose Lean attachment now points
to the upstream theorem. No parent dependency is removed. There is no quarantined
consumer and no other node attached to the retired module.

## Status

landed 20261020T160110-L-3325970 2026-10-20 (merge of deliver/R3/Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite)
