# AlgebraicGeometry.Scheme.root_split_cover_away_divisor_charts

## Reason

Retire the listed Sheaf copy in favour of the existing upstream theorem, as required
by `coord/retire-items.tsv` and the 2026-10-20 retirement hand-off. The copy has no
remaining importer. The upstream theorem has the identical conclusion and drops only
the unused factorization hypothesis `hj`. An `example` with the complete old signature
compiles using exactly `root_split_cover_away_divisor_charts R g n hn p d y hy`.

The upstream theorem and all its source text are preserved. The node now points at
that theorem; its mathematical statement and proof route remain unchanged. No target
statement or definition changes.

## Old

Module: `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts`.

```lean
theorem root_split_cover_away_divisor_charts
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (hj : ∃ j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) (y : Spec R) (hy : g ∉ y.asIdeal) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ (S : CommRingCat.{u}) (φ : R →+* S) (z : Spec S),
      Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      (Spec.map (CommRingCat.ofHom φ)) z = y ∧
      IsUnit (φ g) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin d,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin d,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin d,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))) (φ g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom φ))
```

## New

Module: `WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts`.
The Sheaf module is withdrawn, and the node attaches to this existing declaration:

```lean
theorem root_split_cover_away_divisor_charts
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (d : ℕ) (y : Spec R) (hy : g ∉ y.asIdeal) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ (S : CommRingCat.{u}) (φ : R →+* S) (z : Spec S),
      Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      (Spec.map (CommRingCat.ofHom φ)) z = y ∧
      IsUnit (φ g) ∧
        let N := Spec (CommRingCat.of (Fin d →
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (Fin d →
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (Fin d →
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))) (φ g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom φ))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts | R8 | Retired; no remaining direct or transitive importers. |
| WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel | unchanged | Already imports the upstream twin and calls its theorem without `hj`; compiled unchanged in this session. |

A whole-library import search finds no import of the Sheaf copy. The only other
Lean occurrence of the theorem name is in the upstream cyclic-chart consumer.
The node `lem-sbc-root-split-cover-away-divisor-charts` now points at the upstream
module. Both existing proof-dependency nodes already point at upstream modules.
No forced adaptation or consumer modification is necessary.

## Status

landed 20261020T135423-L-1821434 2026-10-20 (merge of deliver/R8/Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts)
