# AlgebraicGeometry.Scheme.etale_noetherian_global_constructibility

## Reason

Restore the module from the quarantine path recorded in coord/rework.tsv. The archived
source has zero holes but does not elaborate against the current upstream library:
`Unknown identifier LocallyClosedStratification` in both theorem statements and the
private geometric lemma. The current upstream `Scheme.Stratification` is a finite
partition by constructible locally closed subsets with the same immersed scheme
representatives. Both original conclusions already require constructibility explicitly.
Replacing the retired structure therefore preserves the mathematical statements.

The current etale affine-local definition was restored by C1 using the DAG's recorded
`FiniteLocallyClosedStratification`, while G3 restored the pro-etale affine-local definition
using the upstream `Stratification`. Merely renaming the retired type is insufficient on
the etale side. Two private concrete constructions bridge these structures: one copies
all data fields and adds the supplied constructibility proofs, the other copies all data
fields and forgets that proof field. The etale proof applies these conversions to the
local witnesses in each direction. Neither construction chooses an object from an
unproved existence theorem. Both theorem proofs remain complete.

All coefficient universes, hypotheses, affine-open tests, sheaf pullbacks, covering-sieve
quantifiers and module local models stay the same. In particular there is no coefficient
set finiteness assumption, no reducedness assumption on the immersed domains, and no
nonemptiness assumption on the partition. No definition or target in Challenge.lean
changes. The semantic reader should check the retained explicit constructibility conjunct
and the two field-by-field conversions against Stacks 095E and 09AJ.

## Old

From the preserved quarantine archive:

```lean
theorem etale_noetherian_global_constructibility
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X)
        R)) :
    IsCoefficientConstructibleEtaleModule X R F ↔
      ∃ S : LocallyClosedStratification X,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
          (smallModelComparisonEtaleTopology.{u, v} (S.domain a)) R
          ((coefficientEtaleFixedPullback.{u, v} (S.immersion a) R).obj
            ((coefficientModelFixedScalars _ R).obj F))
```

```lean
theorem proEtale_noetherian_global_constructibility
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X)
        R)) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X R F ↔
      ∃ S : LocallyClosedStratification X,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        ∀ (a : Fin S.n) (V : coefficientProEtaleSiteModel.{u, v} (S.domain a)),
          ∃ T : Sieve V, T ∈ coefficientProEtaleModelTopology.{u, v} (S.domain a) V ∧
            ∀ (W : coefficientProEtaleSiteModel.{u, v} (S.domain a)) (f : W ⟶ V), T f →
              ∃ M : ModuleCat.{max v (u + 1)} R, Module.FinitePresentation R M ∧
                Nonempty
                  ((((coefficientProEtaleFixedModulePullback.{u, v} (S.immersion a) R).obj
                      ((coefficientModelFixedScalars _ R).obj F)).over W) ≅
                    (constantSheaf
                      ((coefficientProEtaleModelTopology.{u, v} (S.domain a)).over W)
                      (ModuleCat.{max v (u + 1)} R)).obj M)
```

## New

```lean
theorem etale_noetherian_global_constructibility
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X)
        R)) :
    IsCoefficientConstructibleEtaleModule X R F ↔
      ∃ S : Stratification X,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
          (smallModelComparisonEtaleTopology.{u, v} (S.domain a)) R
          ((coefficientEtaleFixedPullback.{u, v} (S.immersion a) R).obj
            ((coefficientModelFixedScalars _ R).obj F))
```

```lean
theorem proEtale_noetherian_global_constructibility
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X)
        R)) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X R F ↔
      ∃ S : Stratification X,
        (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
        ∀ (a : Fin S.n) (V : coefficientProEtaleSiteModel.{u, v} (S.domain a)),
          ∃ T : Sieve V, T ∈ coefficientProEtaleModelTopology.{u, v} (S.domain a) V ∧
            ∀ (W : coefficientProEtaleSiteModel.{u, v} (S.domain a)) (f : W ⟶ V), T f →
              ∃ M : ModuleCat.{max v (u + 1)} R, Module.FinitePresentation R M ∧
                Nonempty
                  ((((coefficientProEtaleFixedModulePullback.{u, v} (S.immersion a) R).obj
                      ((coefficientModelFixedScalars _ R).obj F)).over W) ≅
                    (constantSheaf
                      ((coefficientProEtaleModelTopology.{u, v} (S.domain a)).over W)
                      (ModuleCat.{max v (u + 1)} R)).obj M)
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility
--allow-missing --uses etale_noetherian_global_constructibility
proEtale_noetherian_global_constructibility` reports zero current downstream modules and
zero uses of either theorem. An additional scan of lean/ and quarantine/ finds the three
archived direct importers below; none applies either theorem by name. These archives and
the item's DAG attachment remain needed and are not withdrawn. Their existing unrelated
quarantined dependencies are not restored here. No current consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility | A3 | Restore both equivalences, migrate retired types, add private data-preserving conversions. |
| Sheaf.Paper.AdicStratifiedPerfect | unclaimed, quarantined | Proof-only import; no use of either theorem name; mathematical affine-local/global equivalences preserved. |
| Sheaf.Paper.DirectedGaloisFiniteTensorGenerators | unclaimed, quarantined | Proof-only import; no use of either theorem name; finite global constructibility meaning preserved. |
| Sheaf.Paper.PrimeFieldTensorDevissage | unclaimed, quarantined | Proof-only import; no use of either theorem name; finite global constructibility meaning preserved. |

The DAG parents lem-sfb-adic-stratified-perfect,
lem-per-finite-tor-internal-hom-any-field, lem-per-prime-field-tensor-devissage and
lem-per-directed-galois-finite-tensor-generators continue to use precisely the same
mathematical equivalences. No parent dependency or unit route is changed. The existing
node's Lean record is updated to the current signature; its proof steps record the
explicit conversions. No source-library file is changed.

## Status

landed 20261021T002920-L-1577892 2026-10-21 (merge of deliver/A3/Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility)
