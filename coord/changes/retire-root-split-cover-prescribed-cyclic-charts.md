# AlgebraicGeometry.Scheme.root_split_cover_prescribed_cyclic_charts

## Reason

Retire the duplicate Sheaf module listed in coord/retire-items.tsv. The upstream
module already proves the classification for every point. The Sheaf copy adds only
an unused divisor-point hypothesis `hy`; the upstream theorem therefore proves the
node's statement and every existing application. Both copies currently have exactly
the same imports, including the upstream cyclic chart model and upstream etale
regular divisor base change. The historical PROOFDIFF_UNSAFE import warning does
not describe the current sources.

## Old

The following declaration in `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts` is withdrawn:

```lean
theorem root_split_cover_prescribed_cyclic_charts
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    [IsRegularRing R] (hg : IsSMulRegular R g)
    [IsRegularRing (R ⧸ Ideal.span {g})]
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (hj : ∃ j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) (y : Spec R) (hy : g ∈ y.asIdeal) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ (S : CommRingCat.{u}) (ψ : Spec S ⟶ Spec R) (z : Spec S),
      Etale ψ ∧ ψ z = y ∧
      let h := (Spec.preimage ψ).hom g
      ∃ (m : ℕ) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        IsRegularRing S ∧ IsSMulRegular S h ∧
        IsRegularRing (S ⧸ Ideal.span {h}) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)) h)
        ∃ γ : pullback p ψ ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p ψ
```

## New

Use the existing, unchanged declaration in `WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts`:

```lean
theorem root_split_cover_prescribed_cyclic_charts
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    [IsRegularRing R] (hg : IsSMulRegular R g)
    [IsRegularRing (R ⧸ Ideal.span {g})]
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (hj : ∃ j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) (y : Spec R) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ (S : CommRingCat.{u}) (ψ : Spec S ⟶ Spec R) (z : Spec S),
      Etale ψ ∧ ψ z = y ∧
      let h := (Spec.preimage ψ).hom g
      ∃ (m : ℕ) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        IsRegularRing S ∧ IsSMulRegular S h ∧
        IsRegularRing (S ⧸ Ideal.span {h}) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)) h)
        ∃ γ : pullback p ψ ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p ψ
```

The original node statement and its proof dependencies remain. Its Lean attachment
points to the stronger upstream theorem. The sole direct consumer keeps its full
public signature and uses the upstream theorem without `hgz`. A direct reference to its retained `hy` binder prevents an unused-variable
warning without changing its signature. No target statement
or definition changes. No WeilConjectures file is modified.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts
--uses root_split_cover_prescribed_cyclic_charts` finds nine downstream modules;
only the direct consumer calls this theorem. The item and consumer nodes are the
only DAG mentions of the item node; no quarantined module or unit realization
requires the Sheaf copy. The mathematical dependency is preserved through the
upstream attachment, including for parents whose proofs are unfinished.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart | unclaimed | Private import changed to the upstream theorem; omit the obsolete hgz argument and its proof. Public signature unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts | unclaimed | Indirect consumer across a private import; no declaration or import change required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor | unclaimed | Indirect consumer across a private import; no declaration or import change required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData | unclaimed | Indirect consumer across a private import; no declaration or import change required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart | unclaimed | Indirect consumer across a private import; no declaration or import change required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal | unclaimed | Indirect consumer across a private import; no declaration or import change required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation | unclaimed | Indirect consumer across a private import; no declaration or import change required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | unclaimed | Indirect consumer across a private import; no declaration or import change required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified | unclaimed | Indirect consumer across a private import; no declaration or import change required. |

## Status

landed 20261021T183357-L-1612395 2026-10-21 (merge of deliver/W6/Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts)
