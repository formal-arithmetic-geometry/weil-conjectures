# AlgebraicGeometry.Proj.twist_finiteLocalization_data

## Reason

Complete `retire:Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData` in
`coord/retire-items.tsv`, under the human-approved retirement procedure recorded
in `coord/changes/retire-sheaf-twins-20261020.md`.
The upstream twin already proves the same declaration. The sole signature
change is the name of an unused existential proof binder (`hspan` versus `_`);
the proof bodies are identical. Header attribution and a local unused-variable
lint option are the other textual differences. No mathematical repair is needed.

## Old

Module `Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData` declares:

```lean
theorem twist_finiteLocalization_data
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (hspan : Ideal.span (Set.range g) = ⊤),
      let ρ := fun (a h : B) (ha : a ∣ h) ↦
        IsLocalizedModule.lift (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
          (RingTheory.localizationAway_map_units_of_dvd (M := M) a h ha)
      ∃ t : ∀ i : Fin n, LocalizedModule.Away (g i) M,
        (∀ i j : Fin n,
          ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) =
            ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j)) ∧
        ∀ p : basicOpen 𝒜 f,
          ∃ (i : Fin n)
            (e : LocalizedModule.Away (g i) M →+
              Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal),
            (∀ z : M,
              e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) =
                IsLocalization.map (M := Submonoid.powers f)
                  (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
                  (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
                  (Submonoid.powers_le.mpr p.2) z) ∧
            e (t i) = (s.1 p).1
```

Node `lem-sc-proj-twist-finite-localization-data` points at this duplicate.

## New

Withdraw the duplicate using `deleted.txt`. The existing upstream theorem stays
verbatim in `WeilConjectures.AlgebraicGeometry.ProjTwistFiniteLocalizationData`:

```lean
theorem twist_finiteLocalization_data
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (_ : Ideal.span (Set.range g) = ⊤),
      let ρ := fun (a h : B) (ha : a ∣ h) ↦
        IsLocalizedModule.lift (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
          (RingTheory.localizationAway_map_units_of_dvd (M := M) a h ha)
      ∃ t : ∀ i : Fin n, LocalizedModule.Away (g i) M,
        (∀ i j : Fin n,
          ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) =
            ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j)) ∧
        ∀ p : basicOpen 𝒜 f,
          ∃ (i : Fin n)
            (e : LocalizedModule.Away (g i) M →+
              Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal),
            (∀ z : M,
              e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) =
                IsLocalization.map (M := Submonoid.powers f)
                  (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
                  (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
                  (Submonoid.powers_le.mpr p.2) z) ∧
            e (t i) = (s.1 p).1
```

Redirect the node's `lean.module`, `lean.file`, and verbatim `lean.statement` to
the upstream twin, with an explanatory `lean.note`. The mathematical statement,
all dependency edges, source, proof plan, unit and review history remain intact.
The parent already uses the upstream module, so there is no consumer adaptation.
No adopted source module or target is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData | C4 (this retirement item) | Proved duplicate withdrawn; node points to the same theorem upstream. |
| WeilConjectures.AlgebraicGeometry.ProjTwistFractionDescent | unclaimed | Existing logical consumer already imports the upstream twin; no source change. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData
--uses twist_finiteLocalization_data` reports zero downstream modules. A search
of both library roots and `quarantine/` finds no importer of the duplicate.
The retirement inventory's consumer `Sheaf.AlgebraicGeometry.ProjTwistFractionDescent`
is already absent, and its node now points at the upstream parent. The parent's
proof still uses `lem-sc-proj-twist-finite-localization-data`, whose mathematical
content is retained through the upstream declaration. This is duplicate
retirement, not withdrawal of that dependency.

The previously required retirements of `ProjTwistFiniteLocalRepresentatives` and
`ProjTwistFiniteValues` are complete: both Sheaf files are withdrawn stubs.
Source-closure scans of the upstream twin and parent find no nonempty pair
`Sheaf.X` / `WeilConjectures.X`. A Lean compatibility probe checks the original
Sheaf signature by applying the upstream theorem. A separate axiom probe checks
the upstream theorem and parent against the three allowed axioms.

## Status

landed 20261020T164441-L-3930897 2026-10-20 (merge of deliver/C4/Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData)
