# AlgebraicGeometry.Scheme.pbcUniformLocalModelCohomology

## Reason

Restore the assigned quarantined module from
quarantine/Sheaf/Paper/PbcUniformLocalModelCohomology.lean, as recorded in
coord/rework.tsv (cluster restore at 5f7b33eac, 2026-10-20).
The archived module fails against the current library with unknown identifier
`LocallyClosedStratification` at lines 68, 223 and 316. Its compile also reports a
cascading unsolved goal in uniform_constructible. The original archive was compiled
in the sandbox to confirm these errors (exit 1, 16.7 seconds).

Replace the obsolete name with the current Scheme.Stratification in the two private
helper signatures and the local hcanonical assertion. This matches the stratification
already supplied by IsUniformlyBoundedConstructibleAdicTower and expected by
pbc_levelwise_truncations_constructible. The current stratification retains the finite
partition, immersed stratum schemes, locally closed strata and their images. Its extra
constructibility field is automatic on the Noetherian scheme T, by
Stratification.ofNoetherianSpace in WeilConjectures.ConstructibleSheaf.Defs.
Empty schemes and empty strata require no exception.

The public theorem signature, all proof terms, imports, docstrings, definitions and
instances are restored verbatim. No target signature changes. The existing node
lem-weil-pbc-uniform-local-model-cohomology retains its Lean attachment and complete
proof dependencies: the proof route has not changed. No source-library file or
other group's file is edited.

## Old

The two private signatures and local assertion, verbatim from the archive:

```lean
private theorem uniform_upper (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (a b : ℤ) (_hab : a ≤ b)
    (S : LocallyClosedStratification T)
    (V : ∀ i : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain i))
    (L : ∀ (i : Fin S.n) (j : (V i).I₀),
      AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :
    ∀ n, (M.level n).IsLE b := by

private theorem uniform_constructible (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (a b : ℤ)
    (S : LocallyClosedStratification T)
    (V : ∀ i : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain i))
    (L : ∀ (i : Fin S.n) (j : (V i).I₀),
      AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :
    ∀ n q, IsConstructibleProEtaleCoefficientModuleSheaf T (PbcQuotient d n)
      ((pbcRestrict (pbcLevelConstantComparison T d n).hom).obj
        ((DerivedCategory.homologyFunctor _ q).obj (M.level n))) := by

  have hcanonical : a ≤ b ∧ ∃ S : LocallyClosedStratification T,
      ∀ i : Fin S.n, ∃ V : Sieve (⊤_ (S.domain i).ProEt),
        V ∈ ProEt.topology (S.domain i) (⊤_ (S.domain i).ProEt) ∧
        ∀ (U : (S.domain i).ProEt) (f : U ⟶ ⊤_ (S.domain i).ProEt),
          V f → Nonempty (AdicTowerLocalModel d (U.hom ≫ S.immersion i) C a b) := by
```

## New

```lean
private theorem uniform_upper (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (a b : ℤ) (_hab : a ≤ b)
    (S : Stratification T)
    (V : ∀ i : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain i))
    (L : ∀ (i : Fin S.n) (j : (V i).I₀),
      AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :
    ∀ n, (M.level n).IsLE b := by

private theorem uniform_constructible (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (a b : ℤ)
    (S : Stratification T)
    (V : ∀ i : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain i))
    (L : ∀ (i : Fin S.n) (j : (V i).I₀),
      AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :
    ∀ n q, IsConstructibleProEtaleCoefficientModuleSheaf T (PbcQuotient d n)
      ((pbcRestrict (pbcLevelConstantComparison T d n).hom).obj
        ((DerivedCategory.homologyFunctor _ q).obj (M.level n))) := by

  have hcanonical : a ≤ b ∧ ∃ S : Stratification T,
      ∀ i : Fin S.n, ∃ V : Sieve (⊤_ (S.domain i).ProEt),
        V ∈ ProEt.topology (S.domain i) (⊤_ (S.domain i).ProEt) ∧
        ∀ (U : (S.domain i).ProEt) (f : U ⟶ ⊤_ (S.domain i).ProEt),
          V f → Nonempty (AdicTowerLocalModel d (U.hom ≫ S.immersion i) C a b) := by
```

The public theorem pbcUniformLocalModelCohomology has exactly its archived signature.
The repaired complete module compiles cleanly (exit 0, 10.5 seconds).

## Users

`python3 tools/downstream.py Sheaf.Paper.PbcUniformLocalModelCohomology --uses
pbcUniformLocalModelCohomology` reports unknown module because the module is
quarantined. A source scan of lean/ and quarantine/ finds the following sole direct
consumer. The DAG parent lem-weil-pbc-uniform-reduction-criterion still cites this
node; this restoration preserves that dependency and the unit route.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PbcUniformReductionCriterion (quarantined) | unclaimed | Its forward implication applies the identical public theorem; no adaptation is required. Its own archived rework remains separate. |

The private helper signatures and local assertion are invisible to ordinary importers.
There are no live consumers to adapt and no forced adaptations.

## Status

landed 20261020T221105-L-4142540 2026-10-20 (merge of deliver/C4/Sheaf.Paper.PbcUniformLocalModelCohomology)
