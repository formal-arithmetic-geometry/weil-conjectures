# AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_generic_etale

## Reason

Restore the quarantined item listed in coord/rework.tsv (sync 5f7b33eac,
2026-10-20). The archived module had zero holes but no longer compiled because
its proof imported the retired Sheaf structural-flatness module.

The adopted upstream flatness theorem uses strictHenselization and
strictLocalizationToBase. This item's unchanged interface uses the small
coordinate-ring colimit strictHenselizationRing and
strictHenselizationStructuralMap. Directly importing the upstream flatness module
fails: its public dependency StrictHenselizationStructuralMapExtension declares
strictHenselizationStructuralMap_eq, which conflicts with the small-interface
lemma already imported from Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap.

Use the existing RingHom.Flat.of_isColimit theorem instead, in a fully proved
private helper. The pointed neighbourhood category is cofiltered; its opposite
is filtered. Each neighbourhood's map on global sections is flat. The structural
map equation identifies the composites with b, so the ring-colimit theorem gives
flatness of b. This is the same mathematical argument as the existing structural
flatness result, specialized to the small colimit actually used here.

All public imports, the public theorem signature, and the original mathematical
argument from structural flatness onward are unchanged. There are no new public
declarations, assumptions, definitions, or local holes. No source-library file
changes. Both the restored public theorem and the private flatness helper compile
with axioms exactly propext, Classical.choice, Quot.sound (4.7 seconds).

The node retains its Lean attachment and statement; its proof dependencies now
record the filtered-colimit proof in place of the incompatible flatness import.
The chapter and unit route are unchanged.

## Old

The signature at the quarantine path is:

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

Its proof imported
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat and called
the now-retired small-ring version of strictHenselization_structural_ringHom_flat.

## New

The restored signature is verbatim:

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

The proof imports WeilConjectures.RingTheory.ProEtale.FaithfullyFlat and calls
the private small_strictHenselization_structural_flat proved using its colimit API.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | no local claim; quarantined for separate rework | Its archived import and application at lines 190-192 remain valid with the identical signature. Archive and DAG dependencies preserved. No adaptation required. |

There are no current active Lean importers. tools/downstream.py cannot inventory
an absent quarantined module (it reports unknown module), so both lean/ and
quarantine/ were scanned for imports and uses of the full module and declaration.
The only archived direct consumer is listed above. The corresponding source
modules already use their upstream version and are unchanged.

Incoming DAG references in lem-sbc-strict-hensel-root-tame-normalization and
lem-sbc-root-normalization-generic-source-etale are preserved. No module or
mathematical statement is withdrawn, and no target definition changes.

## Status

landed 20261020T160753-L-3405407 2026-10-20 (merge of deliver/F3/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale)
