# AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_generic_etale

## Reason

Complete the retirement assigned by `coord/retire-items.tsv`, row 2787, under the
human-approved hand-off in `coord/changes/retire-sheaf-twins-20261020.md`.
The item has zero holes. Its proof and its only direct consumer both duplicate
retained upstream theorems, with the small representative-colimit strict
henselization in place of the canonically isomorphic full affine-neighbourhood
colimit. Retire both copies and adapt the first retained small-model consumer,
`StrictHenselRootPurityData`, with a proved private transport lemma.

## Old

The retired item has this exact public signature:

```lean
theorem GaloisCover.strict_hensel_root_normalization_generic_etale
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g → ∀ (hN : IsLocallyNoetherian N),
    letI := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    letI := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∃ (O : N.Opens), j η ∈ O ∧ Etale (a.fromNormalization ∣_ O)
```

The retired direct consumer has this exact public signature:

```lean
theorem GaloisCover.strict_hensel_root_tame_normalization
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g → IsLocallyNoetherian N →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∃ (C : Scheme.{u}) (n : C ⟶ N),
        IsFinite n ∧ Etale (n ∣_ V) ∧
        ∃ (O : N.Opens), j η ∈ O ∧ Etale (n ∣_ O) ∧
        ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
            pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
          ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
            n ∣_ V
```

`StrictHenselRootPurityData` privately imports
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization` and applies
its theorem. That import transitively exposes the item copy and its small-model
finite-normalization dependency.

## New

The two duplicate modules are listed in `deleted.txt`. Their existing DAG nodes
point to the retained upstream declarations, whose exact signatures are:

```lean
theorem GaloisCover.strict_hensel_root_normalization_generic_etale
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    let H := strictHenselization barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g → ∀ (hN : IsLocallyNoetherian N),
    letI := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    letI := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∃ (O : N.Opens), j η ∈ O ∧ Etale (a.fromNormalization ∣_ O)
```

```lean
theorem GaloisCover.strict_hensel_root_tame_normalization
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    let H := strictHenselization barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g → IsLocallyNoetherian N →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∃ (C : Scheme.{u}) (n : C ⟶ N),
        IsFinite n ∧ Etale (n ∣_ V) ∧
        ∃ (O : N.Opens), j η ∈ O ∧ Etale (n ∣_ O) ∧
        ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
            pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
          ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
            n ∣_ V
```

The purity-data module privately imports the upstream tame-normalization module
and supplies a proved private `small_root_tame_normalization` helper. It composes
`b` with `smallStrictHenselizationColimitIso` and verifies compatibility using
`smallStrictHenselizationColimitIso_toBase`. `AdjoinRoot.mapRingEquiv` explicitly
identifies the two root algebras. The spectrum isomorphism identifies their
punctured opens and maps to the base. Transporting the Cartier centre amounts
to flat pullback of its invertible kernel. The supplied generic point stays in
the same integral regular divisor. Compose the upstream finite model with the
spectrum isomorphism and transport its etale open. A pullback map induced by the
restricted spectrum isomorphism transports the cover comparison, with its
projection equation checked directly. This preserves the public purity-data
statement verbatim and introduces no public declaration or unproved fact.

The source tree under `lean/WeilConjectures/` is unchanged. No definition used by
a target and no target statement changes. The original root-extension,
Abhyankar, finite-normalization and purity route is preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | G8 | Assigned duplicate retired; node attached to retained upstream theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | Only direct consumer retired with its node attached to retained upstream theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Replace the private import and application with a fully proved canonical transport; public signatures identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Transitive consumer; no source or interface change, recompiled against the adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Transitive consumer; no source or interface change, recompiled against the adaptation. |

The table covers every module listed by `tools/downstream.py --uses` for either
retired module, including the complete direct importer graph. Neither retired
node realizes a unit statement or a unit step. The tame-normalization parent
continues to depend on the generic-etaleness node; its attachment is now the
retained upstream theorem. The purity-data parent continues to use the
same tame-normalization node through the canonical transport.

## Status

landed 20261021T173335-L-3588311 2026-10-21 (merge of deliver/G8/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale)
