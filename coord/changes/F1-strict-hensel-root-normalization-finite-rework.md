# AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_finite

## Reason

Restore the module archived at the quarantine path in its current coord/rework.tsv row.
The recorded failure is the unknown identifier
`strictHenselization_structural_ringHom_flat`. Its old Sheaf module was retired.
The replacement upstream theorem concerns a canonically isomorphic coordinate ring,
and importing it together with the current statement dependencies fails:

```text
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension failed,
environment already contains 'AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq'
from Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
```

Keep the existing statement and public imports exactly. Replace the retired private
proof import with `WeilConjectures.RingTheory.ProEtale.FaithfullyFlat`. Prove the flatness
needed by `hf.of_flat` directly on the existing small affine diagram with
`RingHom.Flat.of_isColimit`. The structure maps of the etale neighbourhoods are flat;
the characterization of `strictHenselizationStructuralMap` identifies their composites
with the colimit coprojections with b. This is the same filtered-colimit argument as
the former flatness lemma, without changing any coordinate-ring construction.
The rest of the archived normalization proof is preserved verbatim.

## Old

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

The proof imports
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat` and contains:

```lean
  have : Module.Flat R H := strictHenselization_structural_ringHom_flat R barY b hb
```

## New

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

The signature is identical, including universes, all hypotheses and all let binders.
Only the proof import and the flatness subproof change. The new subproof constructs
the natural stage maps, supplies the actual colimit cocone, proves its stage maps flat,
and checks the composite equation by faithfulness of Spec. It contains no holes.
The assigned module compiled through lcompile.py in 7.8 seconds, with no warnings. A separate scratch import checked #print axioms for the public
theorem: exactly propext, Classical.choice and Quot.sound, with no sorryAx.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | F1 | Restored from quarantine, with its public interface and existing proof retained except for the repaired flatness argument. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | quarantined; no current claim found | Its archived application at line 188 retains exactly the original arguments and conclusion. No adaptation is required. Its archive, rework assignment and DAG dependency are preserved. |

`tools/downstream.py --allow-missing --uses strict_hensel_root_normalization_finite`
finds zero active Lean consumers. The quarantined consumer was checked separately;
its DAG node still cites this item. The unit spreading route and the node's Lean
attachment are retained. No source-library declaration, public import, definition,
or target statement changes.

## Status

landed 20261020T160752-L-3405035 2026-10-20 (merge of deliver/F1/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite)
