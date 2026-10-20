# AlgebraicGeometry.Scheme.exists_etale_separated_stratified_finite

## Reason

Retire the duplicate listed by `retire:Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite`
in coord/retire-items.tsv. The adopted source module already proves exactly the same theorem:
the entire theorem signature and proof are byte-identical. Its axiom check gives only
propext, Classical.choice and Quot.sound. No adopted source module is changed.

## Old

The following declaration was supplied by
Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite:

```lean
theorem exists_etale_separated_stratified_finite {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [QuasiCompact j] :
    ∃ S : Stratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      (∀ i : Fin S.n,
        IsFinite (pullback.snd j (S.immersion i)) ∧
        Etale (pullback.snd j (S.immersion i)))
```

## New

The byte-identical declaration and complete proof are supplied by
WeilConjectures.AlgebraicGeometry.EtaleSeparatedStratifiedFinite. Withdraw the duplicate
Sheaf module through deleted.txt, redirect the sole direct importer privately, and attach
lem-weil-pbc-etale-separated-stratified-finite to the upstream declaration. No mathematical
statement, proof dependency, unit realization, definition or target type changes.

## Users

A source scan of lean/ and quarantine/ finds one direct importer, the unclaimed module
Sheaf.AlgebraicGeometry.EtaleStratifiedFinite. Its only edit replaces the private proof
import with the upstream module. No quarantined consumer exists. The following table
includes every transitive module listed by tools/downstream.py --uses
exists_etale_separated_stratified_finite, as well as the retired item.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite | C4 | Withdraw duplicate; attach node to unchanged upstream theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleExtFilteredColimit | unclaimed | Unchanged exposed interfaces; no edit required. |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | unclaimed | Private import redirected to the upstream module; signatures and proofs unchanged; compiled. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel | unclaimed | Unchanged exposed interfaces; no edit required. |
| Sheaf.AlgebraicGeometry.NoetherianAffineFreePresentation | unclaimed | Unchanged exposed interfaces; no edit required. |
| Sheaf.AlgebraicGeometry.NoetherianConstructibleGaloisPartition | unclaimed | Unchanged exposed interfaces; no edit required. |
| Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel | unclaimed | Unchanged exposed interfaces; no edit required. |
| Sheaf.AlgebraicGeometry.NoetherianEtaleSumConstructible | unclaimed | Unchanged exposed interfaces; no edit required. |
| Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage | unclaimed | Unchanged exposed interfaces; no edit required. |
| Sheaf.DeligneLaumon.NoetherianConstructibleFlatLifting | unclaimed | Unchanged exposed interfaces; no edit required. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Unchanged exposed interfaces; no edit required. |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | Unchanged exposed interfaces; no edit required. |

The actual dependency parents are lem-weil-pbc-etale-stratified-finite,
lem-weil-pbc-etale-affine-cover-gluing and det-lem-stratified-lattice-trace. They retain
the same dependency on the same node and declaration. The affine-cover source theorem
already imports the upstream module; the lattice-trace node has no Lean attachment yet.
Neither requires adaptation. No unit realized route names this item directly; the
constructible finite-etale machinery required by sk-thm-p1 is preserved in full.
The numerous blueprint.from references to this node describe provenance, not parent
proof dependencies. No DAG node is deleted.

## Status

landed 20261020T164812-L-3966793 2026-10-20 (merge of deliver/C4/Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite)
