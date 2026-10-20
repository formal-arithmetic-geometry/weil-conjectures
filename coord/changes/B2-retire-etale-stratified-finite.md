# AlgebraicGeometry.Scheme.exists_etale_stratified_finite

## Reason

Complete the listed retirement repair in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.EtaleStratifiedFinite`. Its adopted-source twin
`WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite` is byte-identical from the
`module` header, including the complete proof, all public imports and private helpers.
The existing upstream theorem is the replacement argument, with exactly the same
hypotheses, conclusion, universe and dependencies. No upstream file is edited.

## Old

In `Sheaf.AlgebraicGeometry.EtaleStratifiedFinite`:

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

Five live consumers privately import the duplicate module.

## New

In `WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite`:

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

Redirect those five private imports to this existing upstream implementation. Withdraw
only the duplicate Sheaf module using `deleted.txt`, and update the existing node's
`lean.module` and `lean.file` to the upstream module, marking it `existing: true`.
The Lean declaration name, statement and complete proof remain the same.

## Users

The table contains every downstream module reported by
`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleStratifiedFinite --uses
AlgebraicGeometry.Scheme.exists_etale_stratified_finite`, plus the item itself.
At inspection all live consumers below were unclaimed. Each adaptation replaces the private import of the retired item. Server preflight also
requires removing the unused private import
`Sheaf.AlgebraicGeometry.FiniteEtalePushforwardFiniteType` from
`NoetherianAffineFreePresentation` and `NoetherianEtaleSumConstructible`: the module is
listed in `coord/route-pivot-dropped-modules.txt`. These two files contain no actual
Lean reference to its declaration, and their existing theorem bodies remain `sorry`.
The mathematical dependency in their proof plans is not claimed solved or bypassed.
That node and module are untouched. The adapted files compile without this import.
Their public imports, declaration signatures, visibility,
definition bodies and theorem proofs remain byte-identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | B2 | Withdraw duplicate; zero holes; retain theorem upstream. |
| Sheaf.AlgebraicGeometry.ConstructibleExtFilteredColimit | unclaimed | Indirect consumer; no edit; identical public interface. |
| Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel | unclaimed | Replace sole private import; proof and signatures unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianAffineFreePresentation | unclaimed | Redirect item import; drop unused route-pivot import; proof and signatures unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianConstructibleGaloisPartition | unclaimed | Replace sole private import; proof and signatures unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel | unclaimed | Indirect consumer; no edit; identical public interface. |
| Sheaf.AlgebraicGeometry.NoetherianEtaleSumConstructible | unclaimed | Redirect item import; drop unused route-pivot import; proof and signatures unchanged. |
| Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage | unclaimed | Indirect consumer; no edit; identical public interface. |
| Sheaf.DeligneLaumon.NoetherianConstructibleFlatLifting | unclaimed | Indirect consumer; no edit; identical public interface. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | Replace sole private import; proof and signatures unchanged. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Indirect consumer; no edit; identical public interface. |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | Indirect consumer; no edit; identical public interface. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Indirect consumer; no edit; identical public interface. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | Indirect consumer; no edit; identical public interface. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | Indirect consumer; no edit; identical public interface. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | Indirect consumer; no edit; identical public interface. |

The only live downstream textual theorem use is the unchanged application in
`FrobeniusVectorBundleKernel`. The other four direct consumers cite it in their proof
plans, and still import the identical theorem for their eventual proofs.

All twelve actual DAG parents were checked. They remain dependent on the same node,
whose attachment now resolves to the identical upstream theorem: no parent edge needs
removing or replacing. These parents are
`lem-sfb-topological-stratified-lisse-lattices`, `lem-trf-coherent-set-criterion`,
`sk-lem-stratified-lattice`, `lem-per-noetherian-constructible-galois-partition`,
`lem-per-noetherian-affine-free-presentation`, `lem-per-noetherian-etale-sum-constructible`,
`lem-weil-pbc-etale-free-sheaf-constructible-core`,
`new-constructible-affine-free-presentation-general`,
`lem-weil-pbc-lisse-e-constructible-integral-lattice`,
`lem-weil-pbc-continuous-lisse-stratified-lattices`,
`new-constructible-limit-descent-general`, and
`lem-weil-pbc-frobenius-vector-bundle-kernel`.

The adopted-source parents `EtaleLowerShriekConstantConstructible`,
`ConstructibleAffineFreePresentationGeneral`, and `ConstructibleLimitDescentGeneral`
already use the upstream module and need no edit. The sk-thm-p1 unit statement and
realized steps remain intact, as does the full constructible finite-etale argument.
No mathematical node, proof dependency, definition or target is withdrawn.

The preserved quarantine archives `Sheaf.Paper.TopologicalStratifiedLisseLattices`,
`Sheaf.Paper.ContinuousLissePullbackSystem`,
`Sheaf.Paper.ContinuousLisseStratifiedLattices`,
`Sheaf.Paper.LisseEConstructibleIntegralLattice`, and `Sheaf.Paper.StratifiedLattice`
contain the historical private import. They are absent from the live library and are
not restored, edited or deleted in this repair. Their eventual rework must replace
that import by `WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite`; the same node,
statement and proof are retained for them. Their quarantine paths and Lean attachments
remain preserved. No already-absent quarantined path is listed in `deleted.txt`.

The upstream replacement passed a single-file exact-statement example;
`#print axioms AlgebraicGeometry.Scheme.exists_etale_stratified_finite` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Status

landed 20261020T235541-L-1188623 2026-10-20 (merge of deliver/B2/Sheaf.AlgebraicGeometry.EtaleStratifiedFinite)
