# AlgebraicGeometry.Scheme.exists_picardSingleRankUnrestrictedPerfectChart

## Reason

Consolidate the duplicate local Cech-chart construction into the already proved
same-unit exists_properFlatDirectImagePerfectChart theorem. This removes 80 proof
lines and the direct import all of PerfectCohomologyFromGeometric. N2 already landed
the original quarantine import repair before this claim. No definition, statement,
instance, attribute or public import changes; no target semantic review is reopened.

## Old

The unchanged signature is:

```lean
theorem exists_picardSingleRankUnrestrictedPerfectChart
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [∀ (T : Scheme.{u}) (U : T.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] (s : S) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ (K : schemeDerivedCategory U.toScheme) (b : ℤ) (r : ℕ),
      IsPerfect U.toScheme K ∧
      (∀ M : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
        ∀ i : ℤ, i < 0 ∨ b < i →
          schemeDerivedTensorCohomologyVanishes U.toScheme K M i) ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
        PicardUniversalSingleRankMatch f E F (g ≫ U.ι) ↔
          ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
            SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) 0).obj
                  ((derivedPullback (h ≫ g)).obj K)) r
```

Its fixed-rank branch constructed the chart in an 80-line local hchart proof.

## New

The signature above remains verbatim. The fixed-rank branch now starts with:

```lean
  · obtain ⟨V, hsV, hVU, K, b, hK, hb, hcomp⟩ :=
      exists_properFlatDirectImagePerfectChart f F U s hsU
```

The rank-transfer proof and zero-object alternative are preserved. The three direct
proof imports listed in report.md are replaced by a private proof import of
Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart. The item's DAG proof follows
this reuse; its statement, attachment, source and unit are unchanged.

## Users

The downstream script reports zero live downstream modules and the declaration in the
item itself. Searching lean/ and quarantine/ also finds the archived direct consumer
below. No user adaptation is necessary because both signature and public imports stay
verbatim. No parent dependency is removed and no quarantined module is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | E2 | Same theorem, shorter proof. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | quarantined; not edited | Same chart theorem application and fields; no adaptation. |

## Status

landed 20261022T002355-L-1921767 2026-10-22 (merge of deliver/E2/Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart)
