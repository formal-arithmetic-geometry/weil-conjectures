# AlgebraicGeometry.Scheme.PbcSuppliedModelCohomologyFlat

## Reason

Restore the assigned module from quarantine/Sheaf/Paper/AdicTorFlatCohomology.lean,
recorded in coord/rework.tsv. Its preserved source has zero sorry holes but fails to
elaborate: line 171 refers to the retired LocallyClosedStratification abbreviation.
The compiler then reports a heartbeat error at line 182 and an unknown predicate
name at line 285. Replacing that one type name resolves all three diagnostics,
without changing resource limits.

The landed record coord/changes/F9-retire-locally-closed-stratification.md gives the
old definition verbatim: abbrev LocallyClosedStratification (X : Scheme.{w}) :=
Stratification X. Thus this replacement expands an abbreviation; it does not change
the predicate's elaborated meaning, even for arbitrary schemes. The current
BoundedConstructibleTower and AdicSuppliedModelFlatCriterion already use
Scheme.Stratification. The latter's landed J2 change record explicitly calls for
this separate restoration. Bounds, covering sieves, local-model systems, coefficient
rings, universes and both theorem signatures are preserved. Empty schemes, empty
strata, zero complexes and arbitrary bounds still have exactly the same quantifiers.

## Old

```lean
def PbcSuppliedModelCohomologyFlat (K : PbcCompletedDerived T d) : Prop :=
  ∀ (d₀ d₁ : ℤ), d₀ ≤ d₁ → ∀ (S : LocallyClosedStratification T)
    (V : ∀ α : Fin S.n, Sieve (⊤_ (S.domain α).ProEt)),
    (∀ α : Fin S.n, V α ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt)) →
    ∀ L : ∀ (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt),
        V α f → AdicTowerLocalModel d (U.hom ≫ S.immersion α)
          (pbcReductionAdicTower T d K) d₀ d₁,
      ∀ (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt)
        (hf : V α f) (q : ℤ),
        SheafOfModules.IsFlatOnSite (J := ProEt.topology U.left)
          (R := (adicTowerInverseImage (U.hom ≫ S.immersion α)).obj (pbcAdicCompletion T d))
          ((DerivedCategory.homologyFunctor _ q).obj
            (DerivedCategory.Q.obj (L α U f hf).complex))
```

## New

```lean
def PbcSuppliedModelCohomologyFlat (K : PbcCompletedDerived T d) : Prop :=
  ∀ (d₀ d₁ : ℤ), d₀ ≤ d₁ → ∀ (S : Stratification T)
    (V : ∀ α : Fin S.n, Sieve (⊤_ (S.domain α).ProEt)),
    (∀ α : Fin S.n, V α ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt)) →
    ∀ L : ∀ (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt),
        V α f → AdicTowerLocalModel d (U.hom ≫ S.immersion α)
          (pbcReductionAdicTower T d K) d₀ d₁,
      ∀ (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt)
        (hf : V α f) (q : ℤ),
        SheafOfModules.IsFlatOnSite (J := ProEt.topology U.left)
          (R := (adicTowerInverseImage (U.hom ≫ S.immersion α)).obj (pbcAdicCompletion T d))
          ((DerivedCategory.homologyFunctor _ q).obj
            (DerivedCategory.Q.obj (L α U f hf).complex))
```

## Users

The source-only downstream tool reports `unknown module(s)` for this quarantined
item. A search also checks all Lean files in both lean/ and
quarantine/ for its exact module and declaration names. Only the item's own archive
mentions the predicate or either theorem; no external direct consumer needs editing.
The independent supplied-model criterion spells out this same predicate and its
existing exact application compiles with the repaired definition.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicTorFlatCohomology | A4 | Restore the complete archived module; expand the retired alias in PbcSuppliedModelCohomologyFlat. Both existing theorem proofs compile unchanged. |
| Sheaf.Paper.IntegralCanonicalTruncations (quarantined) | not adapted | Private importer only; no textual use of the predicate or either theorem. Expanding the alias preserves its available interface. Its archived source is retained for separate restoration. |
| Sheaf.Paper.AdicTorFlatCriterion | not adapted | Mentions the module in its docstring only; no import of or reference to its declarations. |
| Sheaf.Paper.AdicSuppliedModelFlatCriterion | not adapted | Already uses Stratification. Its conclusion is definitionally the repaired predicate; no source change. |

No target statement or elaborated definition changes. The item DAG attachment,
all parent references, proof steps, dependencies and sk-rem-rest route are retained.
No module is withdrawn. The old archive is left for the maintainer's restoration
machinery; this packet supplies the repaired live Lean path.

## Status

landed 20261021T002115-L-1486206 2026-10-21 (merge of deliver/A4/Sheaf.Paper.AdicTorFlatCohomology)
