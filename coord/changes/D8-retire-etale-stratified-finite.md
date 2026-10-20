# AlgebraicGeometry.Scheme.exists_etale_stratified_finite

## Reason

Retire the duplicate explicitly listed in coord/retire-items.tsv and coord/queue.tsv.
The adopted source module already has exactly the same theorem and complete proof.
The complete declaration section, including all private helpers, is byte-identical.
Fresh upstream compilation and axiom printing confirm only propext, Classical.choice
and Quot.sound. No source-library file is edited.

## Old

Provider: Sheaf.AlgebraicGeometry.EtaleStratifiedFinite.

```lean
theorem exists_etale_stratified_finite {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (j : U ⟶ X) [Etale j] :
    ∃ S : Stratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      (∀ i : Fin S.n,
        IsFinite (pullback.snd j (S.immersion i)) ∧
        Etale (pullback.snd j (S.immersion i)))
```

## New

The identical signature and complete proof are supplied by
WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite. Withdraw the duplicate through
deleted.txt; repoint lem-weil-pbc-etale-stratified-finite's lean.module and lean.file only.
The five current direct consumers replace their private import with that provider.
Two consumers also drop an unused private import of
Sheaf.AlgebraicGeometry.FiniteEtalePushforwardFiniteType, which is listed in
coord/route-pivot-dropped-modules.txt and was rejected by the first preflight.
Their existing proofs are admitted and do not reference its declaration.
All signatures, attributes, public imports, proof bodies, definitions, target statements,
DAG mathematical statements, dependency lists and unit realizations are preserved.

## Users

Exact source scans of lean/ and quarantine/ find five live direct importers and five
quarantined direct importers. tools/downstream.py reports fifteen live transitive users.
The table includes that complete set, the retiring item and the five archived users.
Only the five live direct importers are edited; all are unclaimed at preparation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | D8 | Withdraw duplicate; preserve upstream declaration. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel | unclaimed | Redirect private import; all other text unchanged except the two unused policy-dropped imports noted above; compiled. |
| Sheaf.AlgebraicGeometry.NoetherianAffineFreePresentation | unclaimed | Redirect private import; all other text unchanged except the two unused policy-dropped imports noted above; compiled. |
| Sheaf.AlgebraicGeometry.NoetherianConstructibleGaloisPartition | unclaimed | Redirect private import; all other text unchanged except the two unused policy-dropped imports noted above; compiled. |
| Sheaf.AlgebraicGeometry.NoetherianEtaleSumConstructible | unclaimed | Redirect private import; all other text unchanged except the two unused policy-dropped imports noted above; compiled. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | Redirect private import; all other text unchanged except the two unused policy-dropped imports noted above; compiled. |
| Sheaf.AlgebraicGeometry.ConstructibleExtFilteredColimit | unclaimed | Same public dependency interface; no edit. |
| Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel | unclaimed | Same public dependency interface; no edit. |
| Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage | unclaimed | Same public dependency interface; no edit. |
| Sheaf.DeligneLaumon.NoetherianConstructibleFlatLifting | unclaimed | Same public dependency interface; no edit. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Same public dependency interface; no edit. |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | Same public dependency interface; no edit. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Same public dependency interface; no edit. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | Same public dependency interface; no edit. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | Same public dependency interface; no edit. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | Same public dependency interface; no edit. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | quarantined; restoration pending | Archive preserved; same dependency node now resolves upstream. On restoration redirect its obsolete private import to the upstream provider. |
| Sheaf.Paper.ContinuousLissePullbackSystem | quarantined; restoration pending | Archive preserved; same dependency node now resolves upstream. On restoration redirect its obsolete private import to the upstream provider. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | quarantined; restoration pending | Archive preserved; same dependency node now resolves upstream. On restoration redirect its obsolete private import to the upstream provider. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | quarantined; restoration pending | Archive preserved; same dependency node now resolves upstream. On restoration redirect its obsolete private import to the upstream provider. |
| Sheaf.Paper.StratifiedLattice | quarantined; restoration pending | Archive preserved; same dependency node now resolves upstream. On restoration redirect its obsolete private import to the upstream provider. |

The five archives are preserved at their existing quarantine paths, with their rework
rows and Lean attachments intact. This delivery does not restore them or claim their
absence means withdrawal. Their mathematical dependency remains precisely the same
node and theorem; their unrelated quarantine reasons are unaffected.

All twelve actual DAG parents were checked: the four archived lattice statements,
the coherent-set criterion, the three noetherian constructibility statements,
etale-free-sheaf-constructible-core, constructible affine free presentation,
constructible limit descent and the Frobenius vector-bundle kernel. Their dependency
edges remain valid because the node continues to provide the same theorem. The three
adopted source consumers already import the upstream provider. The unit sk-thm-p1
retains its entire realized route, including the constructible/finite-etale machinery.
No node is deleted and no dependency is pruned from an upstream proof.

## Status

landed 20261020T221126-L-4147402 2026-10-20 (merge of deliver/D8/Sheaf.AlgebraicGeometry.EtaleStratifiedFinite)
