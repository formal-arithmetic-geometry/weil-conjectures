# AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_finite

## Reason

Complete the approved zero-hole retirement in coord/retire-items.tsv, row 2047.
The small-colimit Sheaf copy is replaced by the adopted source theorem. The source
and target statements are untouched. Rechecking the retained packet on 2026-10-22
found that its sole former consumer,
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization,
has already been withdrawn and its DAG node points to the upstream twin.
The landed record G8-retire-strict-hensel-root-normalization-generic-etale.md
documents that retirement and the purity-data consumer adaptation, landing
20261021T173335-L-3588311. The old adaptation is preserved in the sandbox scratchpad.

## Old

The retired small-colimit theorem has this exact signature:

```lean
theorem GaloisCover.strict_hensel_root_normalization_finite
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (_hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (_hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
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
    Etale p → IsFinite a.fromNormalization
```

## New

The retained adopted source theorem has this exact signature:

```lean
theorem GaloisCover.strict_hensel_root_normalization_finite
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
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
    Etale p → IsFinite a.fromNormalization
```

Withdraw the item through deleted.txt. Its mathematical node remains and points to
this unchanged upstream declaration, with the exact upstream Lean signature.
Update its proof account to the existing upstream proof: structural flatness is
supplied by strictHenselization_structural_ringHom_flat rather than reconstructed
on the retired small colimit. The rest of the root-algebra and normalization route
is unchanged. The full-colimit theorem has a complete proof and constructs its data.

No consumer is adapted: searches of Lean sources and quarantine find zero imports
of the retiring copy, and no other Lean source calls its declaration. The sole DAG
parent is lem-sbc-strict-hensel-root-tame-normalization, already attached to
WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization.
That upstream module already imports and applies the requested finite-normalization
twin, so the mathematical parent and the unit route continue to use this result.
This is the explicit retirement authorized by the hand-off, with its current parent
reconciled; no mathematical lemma is withdrawn merely because it lacks importers.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | M2 (assigned) | Withdraw the zero-hole duplicate; attach its node to the existing source theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | already withdrawn | Keep the current empty module; do not restore the obsolete adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unchanged | Current mathematical parent already imports and uses the upstream finite-normalization theorem. |

The current source has no direct or transitive Lean consumer of the retiring copy.
No definition or target changes, no new theorem, and no new sorry are introduced.
The unchanged upstream parent compiled through lcompile.py in 10.9 seconds.
A separate import-and-axiom check compiled in 1.6 seconds and printed only
propext, Classical.choice and Quot.sound for both retained theorems.

## Status

landed 20261021T203711-L-3855879 2026-10-21 (merge of deliver/M2/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite)
