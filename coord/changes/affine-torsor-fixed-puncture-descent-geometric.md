# AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits_geometric

## Reason
The original accepts arbitrary m and K, including an empty fixed-ring product for a nonempty cover. Replace them with the orbit data of the induced action and retain the torsor hypotheses. The first worker accidentally dropped etaleness and unique rotations: H = Q, C = Q(sqrt(2)), G trivial, g = 1, and Y = T = Spec Q then refute its strengthened claim (it would identify Spec Q with Spec C over Q). The corrected statement also includes the over-H projection equation required by descent.

## Old
```lean
theorem affine_torsor_fixed_orbits_geometric
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    [IsFinite j] [Etale j]
    (m : ℕ) (K : Fin m → Subgroup G) (d : ℕ) (hd : m ≤ d) :
    let q := Spec.map (CommRingCat.ofHom (algebraMap H C))
    let V : (Spec (CommRingCat.of C)).Opens :=
      PrimeSpectrum.basicOpen (algebraMap H C (ι g))
    Etale (V.ι ≫ q) →
    (∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b) →
    ∀ (T : Scheme.{u}) (t : T ⟶ Spec R) (k : V.toScheme ⟶ T),
      k ≫ t = V.ι ≫ q ≫ Spec.map (CommRingCat.ofHom ι) →
    ∀ (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t →
    let B := ∀ k : Fin m,
      (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let N := Spec (CommRingCat.of B)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H B))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
    ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme, True
```

## New
```lean
theorem affine_torsor_fixed_orbits_geometric
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    [IsFinite j] [Etale j]
    (hEt : Etale (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C))))
    (hrot : ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b)
    (d : ℕ) (D : FixedOrbitData G d)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (hD : D.action = fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
      p T t k hk d δ hδ) :
    let B := ∀ k : Fin D.m,
      (⨅ ζ : D.stabilizer k,
        AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let N := Spec (CommRingCat.of B)
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
    ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
      θ.hom ≫ V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)) =
        pullback.snd p (Spec.map (CommRingCat.ofHom ι))
```

## Users
| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric` | D3 | replaces the false intermediate theorem with the sourced descent statement; remains a named sorry |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore` | unclaimed | only imports the module; no invocation of the geometric theorem; original compiles unchanged |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent` | unclaimed | original compiles unchanged; no invocation of the geometric theorem |

The downstream.py --uses search finds no caller of the modified theorem. No target signature or definition used in a target signature changes. No caller adaptation is needed.

## Status
landed 20261013T222400-L-1221588 2026-10-13 (merge of deliver/D3/Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric)
