# AlgebraicGeometry.Scheme.HasConstructibleAdicTowerModels

## Reason

The assigned rework row preserves the module at
quarantine/Sheaf/Paper/TowerPreservation.lean and records an unknown-identifier error
at line 65. Restore the entire archive, replacing only the stale
`LocallyClosedStratification` reference with the existing
`FiniteLocallyClosedStratification` and publicly importing its owning module.
The canonical interface is a finite partition by locally closed subsets with
scheme domains and immersions, exactly the node's required data. Using upstream
`Stratification` instead would add constructibility of strata on arbitrary schemes;
this repair does not add that requirement. Existing bounded-constructibility
predicates and their chosen stratifications remain untouched.

## Old

```lean
def HasConstructibleAdicTowerModels {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {d : AdicCoefficientDatum A} (N : AdicTower T d) (a b : ℤ) : Prop :=
  ∃ S : LocallyClosedStratification T,
    ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
      V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
      ∀ (U : (S.domain α).ProEt) (h : U ⟶ ⊤_ (S.domain α).ProEt), V h →
        Nonempty (AdicTowerLocalModel d (U.hom ≫ S.immersion α) N a b)
```

## New

```lean
def HasConstructibleAdicTowerModels {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {d : AdicCoefficientDatum A} (N : AdicTower T d) (a b : ℤ) : Prop :=
  ∃ S : FiniteLocallyClosedStratification T,
    ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
      V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
      ∀ (U : (S.domain α).ProEt) (h : U ⟶ ⊤_ (S.domain α).ProEt), V h →
        Nonempty (AdicTowerLocalModel d (U.hom ≫ S.immersion α) N a b)
```

Additional public import:
`Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`.
Every declaration signature, attribute, and previous public import is retained.
No data is chosen and no theorem is assumed by the repair.

## Users

`tools/downstream.py Sheaf.Paper.TowerPreservation --allow-missing --uses
HasConstructibleAdicTowerModels HasTowerAmplitudeCompatibleModels HasTowerPreservation`
finds zero live downstream modules because the item is quarantined. A separate
source import traversal of both lean/ and quarantine/ finds the nine consumers
below. Whole-word declaration searches find only AmplificationProper's conclusion
outside this module. No consumer requires adaptation; none is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TowerPreservation | H2 | Internal amplitude and preservation predicates retain the same signatures and intended finite locally closed local-model data. |
| Sheaf.Paper.AmplificationProper | unclaimed | Quarantined direct consumer. Its unchanged theorem uses HasTowerPreservation only in its conclusion; compiled against the restored module. |
| Sheaf.Paper.CompletedConstructiblePreservation | unclaimed | Quarantined indirect importer; no occurrence of any changed helper or stratification construction. |
| Sheaf.Paper.CompletedConstructibleReductionControl | unclaimed | Quarantined indirect importer; no occurrence of any changed helper or stratification construction. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | Quarantined indirect importer; no occurrence of any changed helper or stratification construction. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | Quarantined indirect importer; no occurrence of any changed helper or stratification construction. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | Quarantined indirect importer; no occurrence of any changed helper or stratification construction. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | Quarantined indirect importer; no occurrence of any changed helper or stratification construction. |
| Sheaf.Paper.QbarProperBaseChange | unclaimed | Quarantined indirect importer; no occurrence of any changed helper or stratification construction. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Quarantined indirect importer; no occurrence of any changed helper or stratification construction. |

The original AmplificationProper file compiled unchanged as a probe in the same
lcompile set after the restored TowerPreservation, so it used the new sandbox
compiled module. The seven indirect Paper consumers and the UpstreamExtra consumer
use the same unchanged public signatures through that theorem. No Challenge target
signature is edited; the intended TOW condition continues to quantify over all
uniformly bounded constructible adic towers with the same normalization and
finite-level amplitude conditions.

## Status

landed 20261020T174800-L-796466 2026-10-20 (merge of deliver/H2/Sheaf.Paper.TowerPreservation)
