# affine_torsor_fixed_orbits

## Reason

The former interface is false: it universally quantifies arbitrary `m` and `K`
with only `m ≤ d`. Taking `m = 0` and the split degree-one identity cover over
ℚ makes the proposed fixed-ring product a zero ring, with empty spectrum,
whereas the base change is nonempty. The module already contains a checked
Mathlib-only counterexample to exactly this tail of the former interface.

Stacks Tag 03SF uses the actual orbits and stabilizers of the descent action.
The correction chooses them existentially and retains `m ≤ d`. It does not
weaken any target or change the caller's mathematical statement. The corrected
proof descends to the explicitly constructed equivariant algebra, applies the
proved orbit decomposition, and transports the principal open over Spec H.

## Old

```lean
theorem affine_torsor_fixed_orbits
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
    ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
      θ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι))
```

## New

```lean
theorem affine_torsor_fixed_orbits
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
    (d : ℕ) :
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
    ∃ (m : ℕ) (K : Fin m → Subgroup G), m ≤ d ∧
    let B := ∀ k : Fin m,
      (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let N := Spec (CommRingCat.of B)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H B))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
    ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
      θ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore | E3 | Owned statement repair and proof. The private counterexample still checks the former arbitrary-data tail and does not apply the repaired theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent | unclaimed | Forced proof adaptation, preserving every existing signature and visibility: take `m`, `K` from the corrected existential conclusion and discard its bound. |

These are the two textual uses reported by `tools/downstream.py --uses
 affine_torsor_fixed_orbits`. All 138 other transitive importers retain their
interfaces through the unchanged public statement of the adapted parent.
No definition used by a target changes meaning: the equivariant algebra is a
new explicit construction, used only by the proof dependencies. All five
Challenge signatures remain untouched. The unit route is unchanged.

## Status

landed 20261013T222402-L-1222531 2026-10-13 (merge of deliver/E3/Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore)

## Forced adaptations

The original parent uses `affine_torsor_orbit_data` (which can always choose
`m=0`), then assigns every `K` the bottom subgroup. Its old application of the
core theorem supplies `m K d hd` before the etale hypotheses; the corrected
core takes `d` and returns the actual `m K` in its conclusion. The original
parent therefore fails compilation against the corrected core. Only lines
93–97 of its proof change: remove the vacuous enumeration and bottom-subgroup
assignment; obtain `m, K, _hmd, θ, hθ` from the corrected core; return exactly
the original conclusion. The private helpers, statements, imports, visibility,
universes and all other proofs of the parent are unchanged. The delivery tool
also performs this counterfactual compilation independently.
