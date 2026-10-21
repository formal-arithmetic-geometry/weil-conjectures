# AlgebraicGeometry.Scheme.IsSfbStratifiedPerfect

## Reason

The R4 assignment restores `Sheaf.Paper.AdicStratifiedPerfect`, recorded in
`coord/rework.tsv` with the diagnostic:

```text
Sheaf/Paper/AdicStratifiedPerfect.lean:209:8:
Unknown identifier `LocallyClosedStratification`
```

The preserved source is `quarantine/Sheaf/Paper/AdicStratifiedPerfect.lean`.
The landed F9 retirement record gives the old alias verbatim:

```lean
abbrev LocallyClosedStratification (X : Scheme.{w}) := Stratification X
```

The current upstream `WeilConjectures.AlgebraicGeometry.LocallyClosedStratification`
publicly imports the existing constructible-sheaf definitions and `Scheme.Stratification`.
The retired Sheaf module is empty. Expanding the abbreviation repairs elaboration and
preserves the original definition for arbitrary schemes, not just Noetherian ones.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification

def IsSfbStratifiedPerfect (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  ∃ s : LocallyClosedStratification X,
    (∀ α : Fin s.n, Topology.IsConstructible (s.stratum α)) ∧
    ∀ α : Fin s.n, ∃ V : Sieve (⊤_ (s.domain α).ProEt),
      V ∈ ProEt.topology (s.domain α) (⊤_ (s.domain α).ProEt) ∧
        ∀ (U : (s.domain α).ProEt) (f : U ⟶ ⊤_ (s.domain α).ProEt), V f →
          ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
            DerivedCategory.IsPerfectRingComplex (DerivedCategory.Q.obj P) ∧
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
            (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
            Nonempty (sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U K ≅
              sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U
                (sfbCompletedModel X I P))
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification

def IsSfbStratifiedPerfect (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  ∃ s : Stratification X,
    (∀ α : Fin s.n, Topology.IsConstructible (s.stratum α)) ∧
    ∀ α : Fin s.n, ∃ V : Sieve (⊤_ (s.domain α).ProEt),
      V ∈ ProEt.topology (s.domain α) (⊤_ (s.domain α).ProEt) ∧
        ∀ (U : (s.domain α).ProEt) (f : U ⟶ ⊤_ (s.domain α).ProEt), V f →
          ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
            DerivedCategory.IsPerfectRingComplex (DerivedCategory.Q.obj P) ∧
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
            (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
            Nonempty (sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U K ≅
              sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U
                (sfbCompletedModel X I P))
```

These are the only two changes relative to the archived Lean source. Every existing
signature, coefficient construction, covering sieve, finite-projective model condition,
and theorem proof is preserved. In particular the explicit constructibility clause
remains, and the one existing theorem hole is neither closed nor duplicated.

## Users

Searches in both live library roots and `quarantine/Sheaf` for the exact module and all
its declaration names find two external direct users. The source-only downstream tool
also reports zero live direct importers with `--allow-missing --direct`. The DAG parent
scan finds precisely the corresponding two parent nodes; both references remain. Other
rework entries that mention this module record transitive dependency failures.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.AdicStratifiedPerfect` | R4, assigned rework | Restore archive with the two changes above. |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | unclaimed, quarantined | Public importer; its statement uses `IsSfbAdicConstructible`, whose definition is byte-identical. Its proof is still `sorry`; the planned application of the repaired theorem keeps its elaborated type. |
| `Sheaf.Paper.IntegralHeartLocalModel` | unclaimed, quarantined | Private proof importer; no code reference to the repaired stratification predicate. No source adaptation is forced. |

No live consumer requires adaptation, and no adopted-source file changes. No target
statement changes. Restoring a definitionally identical predicate does not change any
downstream mathematical meaning. DAG nodes `def-sfb-adic-stratified-perfect-data` and
`lem-sfb-adic-stratified-perfect` keep their existing attachments, statements, dependencies
and proof plans. All parent references and the `sk-lem-integral-models` unit route remain.

## Validation

The repair is checked by the prescribed remote single-file compiler and delivery
preflight. Search for shorter existing results used the prescribed grep, Lean Finder
and Loogle services; no replacement proof was found or introduced by this repair.

## Status

landed 20261021T111542-L-288233 2026-10-21 (merge of deliver/R4/Sheaf.Paper.AdicStratifiedPerfect)
