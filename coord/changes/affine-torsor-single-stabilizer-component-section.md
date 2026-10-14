# affine_torsor_single_stabilizer_component_section

## Reason

Reviewer X-c85ad, E2: the previous universal identity is false. Take
R=H=C=Q, g=1, ι=id, G trivial, T=Spec Q, Y=T disjoint-union T,
d=2, delta the canonical splitting, x=0, K=G, F=Q and f the inclusion
of component 1. It satisfies all hypotheses, but its composite is the component-1
section, distinct from component 0. Even adding openness and the base equation
would not repair the universal statement.

Replace it by existence of a descent of the selected section into Y, with the base
and factorization equations but without openness. Openness is now a separate
conditional fact. The parent component theorem retains its exact signature.
In the open theorem only the unused let-bound name q is renamed _q, avoiding the
unused-variable warning without suppressing a linter; the elaborated type is unchanged.
No definition or Challenge target is changed.

## Old

```lean
theorem affine_torsor_single_stabilizer_component_section
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
      a (algebraMap H C (ι g)) ≠ 0 → ∃! ζ : G, a.comp (ρ ζ).toRingHom = b)
    (d : ℕ) (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫ Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) (K : Subgroup G)
    (hK : ∀ ζ, ζ ∈ K ↔ fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
      p T t k hk d δ hδ ζ x = x)
    (F : Subalgebra H C)
    (f : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F))
      (PrimeSpectrum.basicOpen (algebraMap H F (ι g))) ⟶
      pullback p (Spec.map (CommRingCat.ofHom ι))) :
    (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      (PrimeSpectrum.basicOpen (algebraMap H F (ι g)))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g)); rfl) ≫ f ≫
      pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
      fixedSplitSection p t k d δ x
```

## New

```lean
theorem affine_torsor_single_stabilizer_component_section
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
    (d : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) (K : Subgroup G)
    (hK : ∀ ζ, ζ ∈ K ↔
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ x = x) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let U : (Spec (CommRingCat.of F)).Opens := PrimeSpectrum.basicOpen (algebraMap H F (ι g))
    let q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g))
        rfl)
    ∃ s : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶ Y,
      s ≫ p = (Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
        Spec.map (CommRingCat.ofHom (algebraMap H F))) ≫
          Spec.map (CommRingCat.ofHom ι) ∧
      q ≫ s = fixedSplitSection p t k d δ x
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSingleStabilizerComponent | C3 | Both open and parent proofs construct the pullback lift from the descended s and apply the separate openness criterion. |

The downstream script lists 144 modules by import closure, but its declaration-use
filter finds only this module. A whole-library rg search confirms no other user of
the changed section declaration. The parent component and open immersion conclusions
remain unchanged, so importers require no adaptations. No target-definition review
is reopened: no definition changes and no Challenge signature changes.

## Status

landed 20261014T020507-L-3809926 2026-10-14 (merge of deliver/C3/Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSingleStabilizerComponent)
