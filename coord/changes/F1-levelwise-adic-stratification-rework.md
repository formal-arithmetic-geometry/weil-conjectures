# AlgebraicGeometry.Scheme.pbc_levelwise_truncations_constructible

## Reason

Restore the module from its recorded quarantine source, as assigned by coord/rework.tsv
(the quarantine event dated 2026-10-20, commit 5f7b33eac). The recorded compiler error is
an unknown identifier `LocallyClosedStratification` in the local-model hypothesis.
The current adopted source exposes `AlgebraicGeometry.Scheme.Stratification` in
WeilConjectures.ConstructibleSheaf.Defs. BoundedConstructibleTower already uses this
notion in IsUniformlyBoundedConstructibleAdicTower.

Replace that obsolete type name with Stratification. It retains the finite partition,
stratum schemes, immersions and their images. The current notion also explicitly records
constructibility of each stratum. On the Noetherian scheme assumed by this theorem,
every locally closed stratum is constructible, as documented and implemented by
Scheme.Stratification.ofNoetherianSpace. Thus the theorem's mathematical hypothesis and
conclusions agree with the source; no case, bound or compatibility condition changes.
This also covers the empty scheme and empty strata.

All public imports and definition bodies are restored verbatim, as are all proofs
except the two final transport simplifications in pbc_levelwise_truncation_transitions.
Those now apply the proved private scalar_unit_transport helper, which is exactly
naturality of the adjunction unit, functoriality and associativity. They use simpa only
with explicit equations instead of the full imported simp set.

The full-module timing investigation also showed repeated timeouts during elaboration.
The file gives the existing reductionRingModulesHasDerivedCategory and
pbcTowers_hasDerivedCategory instances local priority 2000, selecting the generic
standard localization before attempting specialized coefficient presentations. The
instances' values are still exactly HasDerivedCategory.standard; no localization
construction or mathematical object changes.
The final file sets completedAdicDerivedChange and pbcDerivedScalarAdjunction locally
irreducible, retaining their ordinary functor/adjunction API without unfolding their
chosen universal witnesses in dependent expressions. This changes no imported or
exported reducibility attribute: the settings are local to this module. No data body,
instance, definition or target signature changes, and no timeout or resource limit is
raised. A final ordinary full-file compile passed cleanly in 32.7 seconds. All profiling
options and probe diagnostics remain in scratchpad/, outside the delivery's lean/ tree.

No source-library module or other group's module is edited. The node attachment and
proof dependencies remain unchanged: the existing unit-naturality step already
specifies the endpoint transport now factored through the private helper.

## Old

The archived signature (its type name no longer resolves):

```lean
theorem pbc_levelwise_truncations_constructible [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) (m d₀ d₁ : ℤ)
    (N : PbcLevelwiseTruncationData T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m)
    (_hN : PbcIsLevelwiseTruncation T (pbcIntegralDatum l E) N)
    (_hTor : PbcLevelwiseTorVanishing T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m)
    (_hmodels : d₀ ≤ d₁ ∧ ∃ S : LocallyClosedStratification T,
      ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
        V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
        ∀ (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt), V f →
          Nonempty (AdicTowerLocalModel (pbcIntegralDatum l E)
            (U.hom ≫ S.immersion α)
            (pbcReductionAdicTower T (pbcIntegralDatum l E) K) d₀ d₁)) :
    IsUniformlyBoundedConstructibleAdicTower (pbcIntegralDatum l E) N.lower ∧
    IsUniformlyBoundedConstructibleAdicTower (pbcIntegralDatum l E) N.upper ∧
    (∀ (n : ℕ) (q : ℤ), (q < d₀ - 1 ∨ min m d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.lower.level n))) ∧
    (∀ (n : ℕ) (q : ℤ), (q < max (m + 1) (d₀ - 1) ∨ d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.upper.level n)))
```

## New

```lean
theorem pbc_levelwise_truncations_constructible [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) (m d₀ d₁ : ℤ)
    (N : PbcLevelwiseTruncationData T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m)
    (_hN : PbcIsLevelwiseTruncation T (pbcIntegralDatum l E) N)
    (_hTor : PbcLevelwiseTorVanishing T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m)
    (_hmodels : d₀ ≤ d₁ ∧ ∃ S : Stratification T,
      ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
        V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
        ∀ (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt), V f →
          Nonempty (AdicTowerLocalModel (pbcIntegralDatum l E)
            (U.hom ≫ S.immersion α)
            (pbcReductionAdicTower T (pbcIntegralDatum l E) K) d₀ d₁)) :
    IsUniformlyBoundedConstructibleAdicTower (pbcIntegralDatum l E) N.lower ∧
    IsUniformlyBoundedConstructibleAdicTower (pbcIntegralDatum l E) N.upper ∧
    (∀ (n : ℕ) (q : ℤ), (q < d₀ - 1 ∨ min m d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.lower.level n))) ∧
    (∀ (n : ℕ) (q : ℤ), (q < max (m + 1) (d₀ - 1) ∨ d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.upper.level n)))
```

The final file additionally uses these module-local attributes (absent in the archive):

```lean
attribute [local instance 2000] reductionRingModulesHasDerivedCategory
attribute [local instance 2000] pbcTowers_hasDerivedCategory
attribute [local irreducible] completedAdicDerivedChange pbcDerivedScalarAdjunction
```

The existing command-local elaboration options are preserved. There is no new file-wide
profiler setting or change to a resource limit.

## Users

There are no live direct importers under lean/Sheaf or lean/WeilConjectures.
`tools/downstream.py Sheaf.Paper.LevelwiseAdicTruncations --uses
pbc_levelwise_truncations_constructible` reports `unknown module(s)` because the assigned
module is quarantined. A source scan additionally includes all archived direct importers:

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicSuppliedModelFlatCriterion (quarantined) | unclaimed | Uses other preserved declarations or the import; all their signatures and bodies are unchanged. |
| Sheaf.Paper.PbcUniformReductionCriterion (quarantined) | unclaimed | Uses other preserved declarations or the import; all their signatures and bodies are unchanged. |
| Sheaf.Paper.CompletedConstructiblePreservation (quarantined) | unclaimed | Uses other preserved declarations or the import; all their signatures and bodies are unchanged. |
| Sheaf.Paper.PbcUniformLocalModelCohomology (quarantined) | unclaimed | Uses the repaired theorem in its canonical-model bound argument. Its own archived LocallyClosedStratification occurrences also require its separate rework; no live consumer is broken by this restoration. |
| Sheaf.Paper.AdicTorFlatCriterion (quarantined) | unclaimed | Uses other preserved declarations or the import; all their signatures and bodies are unchanged. |
| Sheaf.Paper.IntegralCanonicalTruncations (quarantined) | unclaimed | Uses other preserved declarations or the import; all their signatures and bodies are unchanged. |
| Sheaf.Paper.AdicTorFlatCohomology (quarantined) | unclaimed | Uses other preserved declarations or the import; all their signatures and bodies are unchanged. |

Quarantined consumers remain the subjects of their own rework assignments. No live module
requires a forced adaptation. In particular, restoring these consumers here would be a
separate repair of their own pre-existing source failures, not an adaptation forced by
the current restoration.

## Status

landed 20261020T174750-L-793515 2026-10-20 (merge of deliver/F1/Sheaf.Paper.LevelwiseAdicTruncations)

Single-file lcompile.py on the final complete source: exit code 0, clean, 32.7 seconds.
The delivery preflight additionally performs independent declaration/axiom probes;
no global build is run by this worker.
